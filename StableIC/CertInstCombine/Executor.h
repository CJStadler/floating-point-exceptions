//
//  PerturbationExecutor.h
//  Project
//
//  Created by Gu Yijia on 12/5/17.
//

#ifndef Executor_h
#define Executor_h

#include "../AnnoInstCombine/Perturbation.h"
#include "ExecutionStateMap.h"
#include "SplitStrategy.h"

#include "llvm/IR/InstVisitor.h"
#include "llvm/Support/raw_ostream.h"


#include <map>

namespace raic{
    using Edge = std::pair<llvm::BasicBlock*,llvm::BasicBlock*>; //!< CFG edge.
 
    /// Class to implement the logic of interval analysis and automatic differentiation
    //TODO: handle global variable
    class Executor : public llvm::InstVisitor<Executor> {
    public:
        Executor(llvm::Function *fp, ExecutionStateMap  &value_state_map,
                 llvm::PerturbationMap &perturbation_map, std::set<llvm::Value*> &VSet, SplitStrategy &ss):fp_(fp),
        value_state_map_(value_state_map),
        perturbation_map_(perturbation_map),
        VSet_(VSet),
        split_strategy_(ss){}
        
        void run();

    //private:
    
        //implement integer type operations
        void visitSExt(llvm::SExtInst &I);
        void visitShl(llvm::BinaryOperator &I);
        void visitAdd(llvm::BinaryOperator &I);
        void visitSub(llvm::BinaryOperator &I);
        void visitMul(llvm::BinaryOperator &I);
        
        void visitOr(llvm::BinaryOperator &I);
        void visitAnd(llvm::BinaryOperator &I);
    
        
        // Visitation implementation - Implement interval analysis and automatic differentiation for floating-point
        // instruction types.  The semantics are as follows:
        void visitFAdd(llvm::BinaryOperator &I);
        void visitFMul(llvm::BinaryOperator &I);
        void visitFSub(llvm::BinaryOperator &I);
        void visitFDiv(llvm::BinaryOperator &I);
        
        void visitGetElementPtrInst (llvm::GetElementPtrInst &I);
        void visitStoreInst(llvm::StoreInst &SI);
        void visitLoadInst(llvm::LoadInst &LI);
        void visitAllocaInst(llvm::AllocaInst &I);
        
        
        void visitIntrinsic(llvm::IntrinsicInst &II);
        
        void visitReturnInst(llvm::ReturnInst &I);
        
        void visitBranchInst(llvm::BranchInst &I);
        void visitICmpInst(llvm::ICmpInst &I);
        void visitFCmpInst(llvm::FCmpInst &I);
        void visitPHINode(llvm::PHINode       &I);
        void visitSwitchInst(llvm::SwitchInst  &I);
        void visitSIToFP(llvm::SIToFPInst &I);
        
        void visitBitCastInst(llvm::BitCastInst &I);
        void visitZExtInst(llvm::ZExtInst &I);
        void visitSelectInst(llvm::SelectInst &I);
        
        /// Specify what to return for unhandled instructions.
        void visitInstruction(llvm::Instruction &I) {
            assert(false && "visit unsupported instruction");
        };
        
        void visitCallInst(llvm::CallInst &I);
        
        void addBlockInstToWorklist(llvm::BasicBlock *BB);

    private:
        int getAbstractSize(llvm::Type *ty);
        PointerIndex computeGEP(llvm::GEPOperator *gep);
        
        llvm::Function *fp_; //!< The function where the analysis lives
        ExecutionStateMap &value_state_map_; //!< Map values to abstract values
        llvm::PerturbationMap &perturbation_map_;
        std::set<llvm::Value*> &VSet_;
        SplitStrategy &split_strategy_; //!< Determine the input dimension to split
        llvm::SmallVector<llvm::Instruction *, 256> worklist;
        Edge  curr_executable_edge_;  //!< current executable edge.
    };
}
#endif /* Executor_h */
