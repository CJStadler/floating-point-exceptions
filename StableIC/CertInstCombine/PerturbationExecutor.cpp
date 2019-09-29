//
//  PerturbationExecutor.cpp
//  LLVMCertInstCombine
//
//  Created by Gu Yijia on 12/5/17.
//

#include "PerturbationExecutor.h"

using namespace raic;
using namespace llvm;
using namespace std;

void PerturbationExecutor::run(AbstractState *as, const ValueRange &v, std::set<llvm::Value*> &VSet){
    for(auto i : p_.getDeltas()){
        if(VSet.find(i.first) != VSet.end()){
            continue;
        }
        
        double max_perturbation(0); //we only need to calculate the max perturbation;
        for(auto d : i.second){
            if(ConstantFP *C = dyn_cast<ConstantFP>(d)){
                //max_perturbation += abs(C->getValueAPF().convertToDouble());
                max_perturbation += abs(C->getValueAPF().convertToDouble());
            } else {
                ValueRange v = visit(cast<Instruction>(d));
                
                max_perturbation += max(abs(v.lower()), abs(v.upper()));
                
                //            if(v.upper() < 0){
                //                v = ValueRange(abs(v.upper()), abs(v.lower()));
                //            }
                //            max_perturbation += v;
            }
        }
        as ->addDiff(ValueRange(max_perturbation)/v, i.first);

    }
    //return abstract_I ->addDiff;
}

ValueRange PerturbationExecutor::visitFAdd(BinaryOperator &I){
    Value *A = I.getOperand(0);
    Value *B = I.getOperand(1);
    
    ValueRange A_vr = getOpValueRange(A);
    ValueRange B_vr = getOpValueRange(B);
    return A_vr + B_vr;
}

ValueRange PerturbationExecutor::visitFSub(BinaryOperator &I){
    
    Value *A = I.getOperand(0);
    Value *B = I.getOperand(1);
    
    ValueRange A_vr = getOpValueRange(A);
    ValueRange B_vr = getOpValueRange(B);
    
    return  A_vr - B_vr;
}

ValueRange PerturbationExecutor::visitFMul(BinaryOperator &I){
    
    Value *A = I.getOperand(0);
    Value *B = I.getOperand(1);
    ValueRange A_vr = getOpValueRange(A);
    ValueRange B_vr = getOpValueRange(B);
    
    return A_vr * B_vr;
    
}

ValueRange PerturbationExecutor::visitFDiv(BinaryOperator &I){
    Value *A = I.getOperand(0);
    Value *B = I.getOperand(1);
    ValueRange A_vr = getOpValueRange(A);
    ValueRange B_vr = getOpValueRange(B);
    
    return A_vr / B_vr;
    
}

ValueRange PerturbationExecutor::getOpValueRange(llvm::Value *V){

    ValueRange vr;
    if(value_state_map_.hasAbstractState(V) || isa<Constant>(V)){
        AbstractState *t = value_state_map_.atAbstractState(V);
        vr = t -> getValueRange();
    } else if (auto I = dyn_cast<Instruction>(V)){
        vr = visit(I);
    } else {
        assert(false && "empty abstract state");
    }
    
    return vr;
}
