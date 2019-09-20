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

#include "llvm/IR/Instruction.h"

using namespace llvm;

namespace {
  bool isFloatingPointOp(Instruction& op) {
    if (op.isBinaryOp()) {
      switch(op.getOpcode()) {
        case Instruction::FAdd:
        case Instruction::FSub:
        case Instruction::FMul:
        case Instruction::FDiv:
        case Instruction::FRem:
          return true;
      }
    }

    return false;
  }

  struct ReportExceptions : public FunctionPass {
    static char ID;
    ReportExceptions() : FunctionPass(ID) {}

    virtual bool runOnFunction(Function &func) {
      // Get the function to call from our runtime library.
      LLVMContext &Ctx = func.getContext();
      std::vector<Type*> paramTypes = {Type::getInt32Ty(Ctx)};
      Type *retType = Type::getVoidTy(Ctx);
      FunctionType *checkFuncType = FunctionType::get(retType, paramTypes, false);
      Constant *checkFunc = func.getParent()->getOrInsertFunction("check_for_exception", checkFuncType);

      bool changed = false;

      for (auto &block : func) {
        for (auto &op : block) {
          if (isFloatingPointOp(op)) {
            const llvm::DebugLoc &debugInfo = op.getDebugLoc();
            int line = debugInfo.getLine();
            llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(Ctx);
            llvm::Constant *line_value = llvm::ConstantInt::get(i32_type, line, true);

            // Insert *after* `op`.
            IRBuilder<> builder(&op);
            builder.SetInsertPoint(&block, ++builder.GetInsertPoint());

            // Insert a call to our function.
            Value* args[] = {line_value};
            builder.CreateCall(checkFunc, args);

            changed = true;
          }
        }
      }

      return changed;
    }

  }; // end of struct ReportExceptions
}  // end of anonymous namespace

char ReportExceptions::ID = 0;
static RegisterPass<ReportExceptions> X("report_exceptions",
                                        "Instrument the program to report floating point exceptions.",
                                        false,
                                        false);
