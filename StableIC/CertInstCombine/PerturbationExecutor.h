//
//  PerturbationExecutor.h
//  Project
//
//  Created by Gu Yijia on 12/5/17.
//

#ifndef PerturbationExecutor_h
#define PerturbationExecutor_h

#include "ExecutionStateMap.h"
#include "../AnnoInstCombine/Perturbation.h"

#include "llvm/IR/InstVisitor.h"

namespace raic{
    class PerturbationExecutor : public llvm::InstVisitor<PerturbationExecutor, ValueRange> {
    public:
        PerturbationExecutor(llvm::Perturbation &p, ExecutionStateMap  &value_state_map):p_(p), value_state_map_(value_state_map){};
        
        void run(AbstractState *as, const ValueRange &v, std::set<llvm::Value*> &VSet);
        
        // Visitation implementation - Implement interval analysis on the perturbation
        ValueRange visitFAdd(llvm::BinaryOperator &I);
        ValueRange visitFMul(llvm::BinaryOperator &I);
        ValueRange visitFSub(llvm::BinaryOperator &I);
        ValueRange visitFDiv(llvm::BinaryOperator &I);
        /// Specify what to return for unhandled instructions.
        ValueRange visitInstruction(llvm::Instruction &I);
        
    private:
        ValueRange getOpValueRange(llvm::Value *V);
        
    private:
        
        llvm::Perturbation &p_;
        ExecutionStateMap &value_state_map_; //!< Map values to abstract values;
        ValueRange p_range_;
    };
}
#endif /* PerturbationExecutor_h */
