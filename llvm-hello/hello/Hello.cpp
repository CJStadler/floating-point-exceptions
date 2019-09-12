#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <llvm/IR/DebugLoc.h>
#include <llvm/IR/DebugInfoMetadata.h>

using namespace llvm;

namespace {
  struct Hello : public FunctionPass {
    static char ID;
    Hello() : FunctionPass(ID) {}

    virtual bool runOnFunction(Function &F) {
      // Get the function to call from our runtime library.
      LLVMContext &Ctx = F.getContext();
      std::vector<Type*> paramTypes =
        {Type::getDoubleTy(Ctx), Type::getInt32Ty(Ctx)};
      Type *retType = Type::getVoidTy(Ctx);
      FunctionType *logFuncType = FunctionType::get(retType, paramTypes, false);
      Constant *logFunc = F.getParent()->getOrInsertFunction("logop", logFuncType);

      bool changed = false;

      for (auto &B : F) {
        for (auto &I : B) {
          if (auto *op = dyn_cast<BinaryOperator>(&I)) {
            // TODO: make sure is FP operation.

            Instruction *instruction = dyn_cast<Instruction>(op);
            const llvm::DebugLoc &debugInfo = instruction->getDebugLoc();
            int line = debugInfo->getLine();
            llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(Ctx);
            llvm::Constant *line_value = llvm::ConstantInt::get(i32_type, line, true);

            // Insert *after* `op`.
            IRBuilder<> builder(op);
            builder.SetInsertPoint(&B, ++builder.GetInsertPoint());

            // Insert a call to our function.
            Value* args[] = {op, line_value};
            builder.CreateCall(logFunc, args);

            changed = true;
          }
        }
      }

      return changed;
    }

  }; // end of struct Hello
}  // end of anonymous namespace

char Hello::ID = 0;
static RegisterPass<Hello> X("hello",
                             "Hello World Pass",
                             false,
                             false);
