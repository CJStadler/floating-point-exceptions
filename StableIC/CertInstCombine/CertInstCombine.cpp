//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include "CertInstCombine.h"
#include "ExecutionStateMap.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/IRReader/IRReader.h"


using namespace std;
using namespace llvm;
using namespace raic;

cl::list<DoubleInterval, bool, IntervalParser> InitialConstraints("initialInv", cl::CommaSeparated,
                                    cl::desc("Specify initial interval constraints for each function arguments "));
cl::opt<double> SplitLen("splitLen", cl::desc("Specify the initial split length for input intervals"));

#define DEBUG_TYPE "certinstcombine"

bool CertInstCombine::runOnFunction(Function &F){
    AnnoInstructionCombiningPass& anno_instcombine = getAnalysis<AnnoInstructionCombiningPass>();
    if(anno_instcombine.perturbation_map_.empty()){
        return false;
    }
    
   
    init(F);
   
    ValueRange stableWN(0);

    while(!ss_queue_.empty()){
        SplitStrategy ss(ss_queue_.top());
        ss_queue_.pop();

        if (!ss.splitable()){
            outs() << "The function is Uncertain." << "\n";
            //break;
        }

        vector<SplitStrategy> ss_children = ss.split();
        for(auto sc : ss_children){

            ExecutionStateMap stateMap;
            //init input abstract state
            int i = 0;
            for (Function::arg_iterator ai = F.arg_begin(), ai_e = F.arg_end(); ai != ai_e; ++ai){
                AbstractState *as = stateMap.atAbstractState(ai);
                as -> setValueRange(sc.getInputRange(i));
                if(ai -> getType() -> isFloatingPointTy()){
                    as -> addCondition(ValueRange(1), ai); //to calculate the condition number
                }
                i ++;
            }
            
            for (auto &gv : F.getParent()->getGlobalList()){
                if(gv.getType()->isPointerTy()){
                    PointerType *pt = cast<PointerType>(gv.getType());
                    if(pt -> getElementType() -> isArrayTy()){
                        ArrayType *at = cast<ArrayType>(pt -> getElementType());
                        vector<std::unique_ptr<AbstractState>> &as_array = stateMap.atAggregateState(&gv);
                        as_array.resize(at->getNumElements());
                        if(gv.hasInitializer()){
                            if (ConstantDataArray* initArray = dyn_cast<ConstantDataArray>(gv.getInitializer())){
                                for(int i = 0; i < at -> getNumElements(); i ++){
                                    if(at -> getElementType() -> isIntegerTy()){
                                        ConstantInt *C = cast<ConstantInt>(initArray -> getAggregateElement(i));
                                        AbstractState *as = new AbstractState();
                                        as -> setValueRange(C -> getSExtValue(), C -> getSExtValue());
                                        as_array[i] = unique_ptr<AbstractState>(as);
                                    }else{
                                        ConstantFP *C = cast<ConstantFP>(initArray -> getAggregateElement(i));
                                        double c;
                                        if(&(C -> getValueAPF().getSemantics()) == &(APFloat::IEEEsingle()))
                                            c = C->getValueAPF().convertToFloat();
                                        else
                                            c = C->getValueAPF().convertToDouble();
                                        AbstractState *as = new AbstractState();

                                        as -> setValueRange(c, c);
                                        as_array[i] = unique_ptr<AbstractState>(as);
                                    }
                                }
                            }
                        }
                    }
                } else if(gv.getType() -> isSingleValueType()) {
                    AbstractState *as = stateMap.atAbstractState(&gv);
                    if(gv.hasInitializer()){
                        ConstantFP *C = cast<ConstantFP>(gv.getInitializer());
                        double c;
                        if(&(C -> getValueAPF().getSemantics()) == &(APFloat::IEEEsingle()))
                            c = C->getValueAPF().convertToFloat();
                        else
                            c = C->getValueAPF().convertToDouble();
                        as -> setValueRange(c, c);
                    }
                }
            }
         

            Executor executor(&F, stateMap, anno_instcombine.perturbation_map_, VSet, sc);
            executor.run();
            
            if(!sc.stabilize(VSet, stableWN)){
                ss_queue_.push(sc);
            }

//            DEBUG(dbgs() << "s state" << s_strategy.getTargetAbstractState() << "\n");
//            if(s_strategy.getTargetAbstractState().getPerturbationUpperBound().second > curr_max_mid_cost){
//                if(s_strategy.getMidCost() > curr_max_mid_cost){
//                    curr_max_mid_cost = s_strategy.getMidCost();
//                }
//                ss_queue_.push(s_strategy.getSplitInfoState());
//            }
        }
    }
    
    DEBUG(dbgs() <<  "Wilkinson Number: " << "[" << stableWN.lower() << "," << stableWN.upper() << "]\n");
    return false;
}

PreservedAnalyses CertInstCombinePass::run(Function &F,
                                       FunctionAnalysisManager &AM) {
    FunctionPassManager FPM;
    FPM.addPass(AnnoInstCombinePass());
    FPM.run(F, AM);
    
    // Mark all the analyses that instcombine updates as preserved.
    PreservedAnalyses PA;
    PA.preserveSet<CFGAnalyses>();
    return PA;
}

void CertInstCombine::init(llvm::Function &F) {
    vector<ValueRange> input_ranges;
    initInputsHelp(0, F.arg_size(), input_ranges);
}

void CertInstCombine::initInputsHelp(int index, int size, vector<ValueRange> &input_ranges){
    init_input_len_ = SplitLen;
    if(index < size){
        
        ValueRange vr(InitialConstraints[index].lower_bound, InitialConstraints[index].upper_bound);
        if(boost::numeric::width(vr) < init_input_len_){
            input_ranges.push_back(vr);
            initInputsHelp(index + 1, size, input_ranges);
            input_ranges.pop_back();
        } else {
            int slice_count = std::ceil(boost::numeric::width(vr) / init_input_len_);
            for(int i = 0; i < slice_count; i ++){
                double lower = vr.lower() + init_input_len_ * i;
                double upper = vr.lower() + init_input_len_ * (i + 1);
                if(upper > vr.upper()){
                    upper = vr.upper();
                }
                input_ranges.push_back(ValueRange(lower, upper));
                initInputsHelp(index + 1, size, input_ranges);
                input_ranges.pop_back();
            }
        }
    }else{
        ss_queue_.push(SplitStrategy(input_ranges));
    }
}


char CertInstCombine::ID = 0;
static RegisterPass<CertInstCombine> X("certinstcombine", "Certified InstCombine Pass");



