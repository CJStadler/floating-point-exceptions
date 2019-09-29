#include <limits>

#include "Executor.h"
#include "ExecutionStateCalculation.h"

#include "llvm/Support/Debug.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstIterator.h"

using namespace std;
using namespace llvm;
using namespace raic;

#define DEBUG_TYPE "executor"

void Executor::run(){
    DEBUG(dbgs() <<"Number of perturbed instructions: " << perturbation_map_.size() << "\n");
    addBlockInstToWorklist(&fp_->getEntryBlock());
    while(!worklist.empty()){
        auto I = worklist.begin();
        DEBUG(dbgs() << "visit inst:" << **I << "\n");
        visit(*I);
        worklist.erase(I);
    }
    
    //outs() << *value_state_map_.atAbstractState(target_var_);
    //for(auto i : value_state_map_.atAbstractState(target_var_) -> getDifferentialMap()){
    //    outs() << "Line Number: " << perturbation_map_[i.first].getLineNumber() << "\n";
    //}
}

void Executor::visitSExt(llvm::SExtInst &I){
    DEBUG(dbgs() << "visit SExt" << "\n");
    value_state_map_.copyValue(I.getOperand(0), &I);
}

void Executor::visitShl(llvm::BinaryOperator &I){
    AbstractState *abstract_A = value_state_map_.atAbstractState(I.getOperand(0));
    AbstractState *abstract_B = value_state_map_.atAbstractState(I.getOperand(1));
    AbstractState *abstract_I = value_state_map_.atAbstractState(&I);
    
    assert((abstract_A -> getValueRange().lower() == abstract_A -> getValueRange().upper()) && "Ambiguous Integer Operation");
    assert((abstract_B -> getValueRange().lower() == abstract_B -> getValueRange().upper()) && "Ambiguous Integer Operation");
    
    int i = abstract_A -> getValueRange().lower();
    int s = abstract_B -> getValueRange().lower();
    i = i << s;
    abstract_I -> setValueRange(i, i);
}

void Executor::visitAdd(BinaryOperator &I){
    DEBUG(dbgs() << "visit Add" << "\n");
    AbstractState *abstract_A = value_state_map_.atAbstractState(I.getOperand(0));
    AbstractState *abstract_B = value_state_map_.atAbstractState(I.getOperand(1));
    AbstractState *abstract_I = value_state_map_.atAbstractState(&I);
    
    ValueRange vr =  abstract_A -> getValueRange() + abstract_B -> getValueRange();
    abstract_I -> clearState();
    abstract_I -> setValueRange(vr);
}

void Executor::visitSub(BinaryOperator &I){
    DEBUG(dbgs() << "visit Sub" << "\n");
    AbstractState *abstract_A = value_state_map_.atAbstractState(I.getOperand(0));
    AbstractState *abstract_B = value_state_map_.atAbstractState(I.getOperand(1));
    AbstractState *abstract_I = value_state_map_.atAbstractState(&I);
    
    ValueRange vr =  abstract_A -> getValueRange() - abstract_B -> getValueRange();
    abstract_I -> clearState();
    abstract_I -> setValueRange(vr);
    
}

void Executor::visitMul(BinaryOperator &I){
    DEBUG(dbgs() << "visit Mul" << "\n");
    AbstractState *abstract_A = value_state_map_.atAbstractState(I.getOperand(0));
    AbstractState *abstract_B = value_state_map_.atAbstractState(I.getOperand(1));
    AbstractState *abstract_I = value_state_map_.atAbstractState(&I);
    
    ValueRange vr =  abstract_A -> getValueRange() * abstract_B -> getValueRange();
    abstract_I -> clearState();
    abstract_I -> setValueRange(vr);
    
}


void Executor::visitOr(llvm::BinaryOperator &I){
    AbstractState *abstract_A = value_state_map_.atAbstractState(I.getOperand(0));
    AbstractState *abstract_B = value_state_map_.atAbstractState(I.getOperand(1));
    AbstractState *abstract_I = value_state_map_.atAbstractState(&I);
    
    assert((abstract_A -> getValueRange().lower() == abstract_A -> getValueRange().upper()) && "Ambiguous Integer Operation");
    assert((abstract_B -> getValueRange().lower() == abstract_B -> getValueRange().upper()) && "Ambiguous Integer Operation");
    
    int i = abstract_A -> getValueRange().lower();
    int s = abstract_B -> getValueRange().lower();
    i = i | s;
    abstract_I -> setValueRange(i, i);
}

void Executor::visitAnd(llvm::BinaryOperator &I){
    AbstractState *abstract_A = value_state_map_.atAbstractState(I.getOperand(0));
    AbstractState *abstract_B = value_state_map_.atAbstractState(I.getOperand(1));
    AbstractState *abstract_I = value_state_map_.atAbstractState(&I);
    
    assert((abstract_A -> getValueRange().lower() == abstract_A -> getValueRange().upper()) && "Ambiguous Integer Operation");
    assert((abstract_B -> getValueRange().lower() == abstract_B -> getValueRange().upper()) && "Ambiguous Integer Operation");
    
    int i = abstract_A -> getValueRange().lower();
    int s = abstract_B -> getValueRange().lower();
    i = i & s;
    abstract_I -> setValueRange(i, i);
}

void Executor::visitFAdd(BinaryOperator &I){
    DEBUG(dbgs() << "visit FAdd" << "\n");
    Value *A = I.getOperand(0);
    Value *B = I.getOperand(1);
    ExecutionStateCalculation::updateAddExecutionState(&I, A, B, value_state_map_, perturbation_map_,VSet_);
}

void Executor::visitFSub(BinaryOperator &I){
    DEBUG(dbgs() << "visit FSub" << "\n");
    Value *A = I.getOperand(0);
    Value *B = I.getOperand(1);
     ExecutionStateCalculation::updateSubExecutionState(&I, A, B, value_state_map_, perturbation_map_,VSet_);
}

void Executor::visitFMul(BinaryOperator &I){
    DEBUG(dbgs() << "visit FMul" << "\n");
    Value *A = I.getOperand(0);
    Value *B = I.getOperand(1);
    ExecutionStateCalculation::updateMulExecutionState(&I, A, B, value_state_map_, perturbation_map_, VSet_);
}

void Executor::visitFDiv(BinaryOperator &I){
    DEBUG(dbgs() << "visit FDiv" << "\n");
    Value *A = I.getOperand(0);
    Value *B = I.getOperand(1);
    ExecutionStateCalculation::updateDivExecutionState(&I, A, B, value_state_map_, perturbation_map_,VSet_);
}

void Executor::visitGetElementPtrInst (llvm::GetElementPtrInst &I){
    DEBUG(dbgs() << "visit GEP" << "\n");
    PointerIndex pi = computeGEP(dyn_cast<GEPOperator>(&I));
    value_state_map_.update(&I, pi);
}

void Executor::visitStoreInst(StoreInst &SI){
    DEBUG(dbgs() << "visit StoreInst" << "\n");
    Value* pointer = SI.getPointerOperand();
    if(ConstantExpr *ceP = dyn_cast<ConstantExpr>(pointer)){
        if(isa<GEPOperator>(ceP)){
            PointerIndex pi = computeGEP(dyn_cast<GEPOperator>(ceP));
            value_state_map_.update(ceP, pi);
            value_state_map_.copyValue(SI.getValueOperand(), ceP);
        }else{
          assert(false && "error");
        }
    } else {
        value_state_map_.copyValue(SI.getValueOperand(), pointer);
    }
}

void Executor::visitLoadInst(LoadInst &LI){
    Value* pointer = LI.getPointerOperand();
    if(isa<ConstantExpr>(pointer)){
        PointerIndex pi = computeGEP(dyn_cast<GEPOperator>(pointer));
        value_state_map_.update(pointer, pi);
        value_state_map_.copyValue(pointer, &LI);
    } else {
        value_state_map_.copyValue(pointer, &LI);
    }
}

void Executor::visitAllocaInst(AllocaInst &I){
    Type *ty = I.getAllocatedType();
    if(ty -> isFloatingPointTy()){
        value_state_map_.atAbstractState(&I);
    }else if(ty -> isIntegerTy()){
        //Do nothing
    }else if(ty -> isAggregateType()){
        vector<std::unique_ptr<AbstractState>> &as_array = value_state_map_.atAggregateState(&I);
        for(int i = 0; i < getAbstractSize(ty); i++){//initialize abstract state
            as_array.push_back(unique_ptr<AbstractState>(new AbstractState()));
        }
        PointerIndex pi;
        pi.base = &I;
        pi.index = 0;
        value_state_map_.update(&I, pi);
    }else if(ty -> isPointerTy()){ //treat pointerTy as aggregate with 1 element
        vector<std::unique_ptr<AbstractState>> &as_array = value_state_map_.atAggregateState(&I);
        as_array.push_back(unique_ptr<AbstractState>(new AbstractState()));
        PointerIndex pi;
        pi.base = &I;
        pi.index = 0;
        value_state_map_.update(&I, pi);
    }else {
        assert(false && "unsupported alloc type");
    }

}

void Executor::visitIntrinsic(IntrinsicInst &II){
    //TODO: handle intrinsics
}

void Executor::visitReturnInst(ReturnInst &I){
    DEBUG(dbgs() << "visit Return instruction" << "\n");
    split_strategy_.setTarget(I.getReturnValue(), *(value_state_map_.atAbstractState(I.getReturnValue())));
}

void Executor::visitBranchInst(BranchInst &I){
    if (I.isUnconditional()){
        DEBUG(dbgs() << "Unconditional branch: " << I << "\n") ;
        curr_executable_edge_ = make_pair(I.getParent(),I.getSuccessor(0));
        addBlockInstToWorklist(I.getSuccessor(0));
        return;
    } // End Unconditional Branch
    
    DEBUG(dbgs() << "Conditional branch: " << I << "\n") ;
    
    // Special cases if constants true or false
    if (value_state_map_.isTrueConstant(I.getCondition())){
        DEBUG(dbgs() << "\tthe branch condition is MUST BE TRUE.\n") ;
        curr_executable_edge_ = make_pair(I.getParent(),I.getSuccessor(0));
        addBlockInstToWorklist(I.getSuccessor(0));
        return;
    }
    
    if (value_state_map_.isFalseConstant(I.getCondition())){
        DEBUG(dbgs() << "\tthe branch condition is MUST BE FALSE.\n") ;
        curr_executable_edge_ = make_pair(I.getParent(),I.getSuccessor(1));
        addBlockInstToWorklist(I.getSuccessor(1));
        return;
    }
    
    assert(false && "undetermined branch instruction");
}
void Executor::visitFCmpInst(FCmpInst &I){
     DEBUG(dbgs() << "visit FCmp instruction" << "\n");
     switch(I.getPredicate()){
         case CmpInst::FCMP_FALSE:
             break;
         case CmpInst::FCMP_OEQ: {
             AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
             AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
             
             if(op1->getValueRange() == op2 -> getValueRange()){
                 value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
             }else{
                 value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
             }
             break;
         }
         case CmpInst::FCMP_OGT: case CmpInst::FCMP_UGT:{
             AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
             AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
             
             if(op1->getValueRange() > op2 -> getValueRange()){
                 value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
             }else{
                 value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
             }
             break;
         }
         case CmpInst::FCMP_OGE:{
             AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
             AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
             
             if(op1->getValueRange() >= op2 -> getValueRange()){
                 value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
             }else{
                 value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
             }
             break;
         }

         case CmpInst::FCMP_OLT: case CmpInst::FCMP_ULT: {
             AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
             AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
             
             if(op1->getValueRange() < op2 -> getValueRange()){
                 value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
             }else{
                 value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
             }
             break;
         }
            
         case CmpInst::FCMP_OLE:{
             AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
             AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
             
             if(op1->getValueRange() <= op2 -> getValueRange()){
                 value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
             }else{
                 value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
             }
             break;
         }
             
         case CmpInst::FCMP_ONE:
             assert(false && "unsupported ICmp instruction");
             break;
         case CmpInst::FCMP_UNE:{
             AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
             AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
             
             if(boost::numeric::empty(boost::numeric::intersect(op1->getValueRange(),  op2 -> getValueRange()))){
                 value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
             }else{
                 value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
             }
             break;
         }
         case CmpInst::FCMP_ORD:
             assert(false && "unsupported ICmp instruction");
             break;
         case CmpInst::FCMP_TRUE:
             assert(false && "unsupported ICmp instruction");
             break;
         default:
             assert(false && "unsupported ICmp instruction");
     }
}
void Executor::visitICmpInst(ICmpInst &I){
    DEBUG(dbgs() << "visit ICmp instruction" << "\n");
    //TODO : assuem signed predicate
    switch(I.getSignedPredicate()){
        
        case CmpInst::ICMP_EQ:{
            
            AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
            AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
            
            if(op1->getValueRange() == op2 -> getValueRange()){
                value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
            }else{
                value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
            }
            break;
        }
        case CmpInst::ICMP_NE:{
            AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
            AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
            
            if(op1->getValueRange() == op2 -> getValueRange()){
                value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
            }else{
                value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
            }
            break;
        }
        case CmpInst::ICMP_SGT:{
            AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
            AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
            
            if(op1->getValueRange() > op2 -> getValueRange()){
                value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
            }else{
                value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
            }
            break;
        }
        case CmpInst::ICMP_SGE:{
            AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
            AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
            
            if(op1->getValueRange() >= op2 -> getValueRange()){
                value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
            }else{
                value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
            }
            break;
        }
        case CmpInst::ICMP_SLT:{
            AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
            AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
            
            if(op1->getValueRange() < op2 -> getValueRange()){
                value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
            }else{
                value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
            }
            break;
        }
        case CmpInst::ICMP_SLE:{
            AbstractState *op1 =  value_state_map_.atAbstractState(I.getOperand(0));
            AbstractState *op2 =  value_state_map_.atAbstractState(I.getOperand(1));
            
            if(op1->getValueRange() <= op2 -> getValueRange()){
                value_state_map_.update(&I, ConstantInt::getTrue(I.getType()));
            }else{
                value_state_map_.update(&I, ConstantInt::getFalse(I.getType()));
            }
            break;
        }
        default:
            assert(false && "unsupported ICmp instruction");
    }
}

void Executor::visitPHINode(PHINode &I){
    DEBUG(dbgs() << "PHI node " << I << "\n");
    for (unsigned i = 0, num_vals = I.getNumIncomingValues(); i != num_vals;i++) {
        // if (!isEdgeFeasible(PN.getIncomingBlock(i), PN.getParent()))
        //   dbgs() << PN.getIncomingBlock(i)->getName()
        //          << " --> " << PN.getParent()->getName()  << " IS UNREACHABLE\n";
        // else{
        //   dbgs() << PN.getIncomingBlock(i)->getName()
        //          << " --> " << PN.getParent()->getName()  << " IS REACHABLE\n";
        // }
        
        if(I.getIncomingBlock(i) == curr_executable_edge_.first){
            Value* v = I.getIncomingValue(i);
            value_state_map_.copyValue(v, &I);
            break;
        }
        
    }
}

void Executor::visitSwitchInst(llvm::SwitchInst  &I){
    AbstractState *cond = value_state_map_.atAbstractState(I.getCondition());
    assert((cond -> getValueRange().lower() == cond -> getValueRange().upper()) && "Ambiguous Switch Condition");
    
    int i = cond -> getValueRange().lower();
    curr_executable_edge_ = make_pair(I.getParent(),I.getSuccessor(i));
    addBlockInstToWorklist(I.getSuccessor(i));
}

void Executor::visitSIToFP(llvm::SIToFPInst &I){
    DEBUG(dbgs() << "visit SIToFP" << "\n");
    value_state_map_.copyValue(I.getOperand(0), &I);
}

void Executor::visitBitCastInst(llvm::BitCastInst &I){
    PointerIndex pi;
    Type* sTy = I.getOperand(0)->getType();
    if(value_state_map_.hasPointerIndex(I.getOperand(0), pi)){
        value_state_map_.update(&I, pi);
    }else{
        value_state_map_.copyValue(I.getOperand(0), &I);
    }
}

void Executor::visitZExtInst(llvm::ZExtInst &I){
    value_state_map_.copyValue(I.getOperand(0), &I);
}

void Executor::visitSelectInst(llvm::SelectInst &I){
    if (value_state_map_.isTrueConstant(I.getCondition())){
        value_state_map_.copyValue(I.getTrueValue(), &I);
    }else{
        value_state_map_.copyValue(I.getFalseValue(), &I);
    }
}

void Executor::visitCallInst(CallInst &I){
    StringRef fnName = I.getCalledFunction()->getName();
    
    if(fnName == "llvm.dbg.declare" || fnName == "llvm.dbg.value"){
        return;
    }
    
    if(fnName == "sin") {
        ExecutionStateCalculation::updateSinExecutionState(&I, I.getOperand(0), value_state_map_, perturbation_map_,VSet_);
    } else if(fnName == "exp" || fnName == "__exp_finite"){
        ExecutionStateCalculation::updateExpExecutionState(&I, I.getOperand(0), value_state_map_, perturbation_map_,VSet_);
    } else if(fnName == "cos") {
        ExecutionStateCalculation::updateCosExecutionState(&I, I.getOperand(0), value_state_map_, perturbation_map_,VSet_);
    } else if(fnName == "tan") {
        ExecutionStateCalculation::updateTanExecutionState(&I, I.getOperand(0), value_state_map_, perturbation_map_,VSet_);
    } else if(fnName == "atan2" || fnName == "__atan2_finite"){
        ExecutionStateCalculation::updateAtan2ExecutionState(&I, I.getOperand(0), I.getOperand(1), value_state_map_, perturbation_map_,VSet_);
    } else if(fnName == "asin" || fnName == "__asin_finite"){
        ExecutionStateCalculation::updateAsinExecutionState(&I, I.getOperand(0), value_state_map_, perturbation_map_,VSet_);
    } else if(fnName == "log"){
        ExecutionStateCalculation::updateLogExecutionState(&I, I.getOperand(0), value_state_map_, perturbation_map_,VSet_);
    } else if(fnName == "llvm.sqrt.f64"){
        ExecutionStateCalculation::updateSqrtExecutionState(&I, I.getOperand(0), value_state_map_, perturbation_map_,VSet_);
    } else {
        assert(false && "Calling Unsupported Function");
    }
}



void Executor::addBlockInstToWorklist(BasicBlock *BB){
    for (Instruction &I : *BB){
         worklist.push_back(&I);
    }
}

int Executor::getAbstractSize(llvm::Type *ty){
    if(ty -> isSingleValueType()){
        return 1;
    }else if(ty -> isArrayTy()){
        return ty -> getArrayNumElements() * getAbstractSize(ty -> getArrayElementType());
    }else if(ty -> isStructTy()){
        int size = 0;
        for(int i = 0; i < ty -> getStructNumElements(); i ++){
            Type *elem_ty = ty -> getStructElementType(i);
            if(elem_ty -> isSingleValueType()){
                size ++;
            }else if(elem_ty -> isArrayTy()){
                size += getAbstractSize(elem_ty);
            }else if(elem_ty -> isStructTy()){
                size += getAbstractSize(elem_ty);
            }
        }
        return size;
        
    }else{
        assert(false && "unsupported type");
    }
}

PointerIndex Executor::computeGEP(llvm::GEPOperator *gep){
    PointerIndex pi;
    if(! value_state_map_.hasPointerIndex(gep -> getPointerOperand(), pi)){
        assert(false && "visit null pointer in GEP");
    }
    Type *ty = gep -> getPointerOperand()->getType();
    
    auto i = gep -> idx_begin();
    if(ConstantInt *C1 = dyn_cast<ConstantInt>(*i)){
        pi.index += getAbstractSize(ty) * (C1 -> getZExtValue());
    }else{
        AbstractState *abstract_index = value_state_map_.atAbstractState(*i);
        assert(abstract_index -> getValueRange().lower() == abstract_index -> getValueRange().upper() && "Ambiguous pointer index");
        pi.index += getAbstractSize(ty) * abstract_index -> getValueRange().lower();
    }
    if(ty -> isPointerTy()){
        Type *pTy = ty -> getPointerElementType();
        if(pTy -> isArrayTy()){
            if(ConstantInt *CI = dyn_cast<ConstantInt>(*(i + 1))){
                pi.index += getAbstractSize(pTy -> getArrayElementType()) * (CI -> getZExtValue());
            }else{
                AbstractState *abstract_index = value_state_map_.atAbstractState(*(i + 1));
                assert(abstract_index -> getValueRange().lower() == abstract_index -> getValueRange().upper() && "Ambiguous pointer index");
                pi.index += getAbstractSize(pTy -> getArrayElementType()) * abstract_index -> getValueRange().lower();
            }
        }else if(pTy -> isStructTy()){
            int elem_index = 0;
            if(ConstantInt *CI = dyn_cast<ConstantInt>(*(i + 1))){
                elem_index = CI -> getZExtValue();
            } else {
                AbstractState *abstract_index = value_state_map_.atAbstractState(*(i + 1));
                assert(abstract_index -> getValueRange().lower() == abstract_index -> getValueRange().upper() && "Ambiguous pointer index");
                elem_index = abstract_index -> getValueRange().lower();
            }
            
            for(int j = 0; j < elem_index; j ++){
                pi.index += getAbstractSize(pTy -> getStructElementType(j));
            }
        }
    }else{
        assert(false && "unsupported alloc type");
    }
    return pi;
}


