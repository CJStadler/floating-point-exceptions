//
//  SplitStrategy.h
//  Project
//
//  Created by Gu Yijia on 12/21/17.
//

#ifndef SplitStrategy_h
#define SplitStrategy_h

#include "AbstractState.h"
#include "SplitInfoState.h"
#include "../AnnoInstCombine/Perturbation.h"

#include <vector>
#include <map>

namespace raic {
    using MidPerturbationMap = std::map<llvm::Value *, std::map<llvm::Value *, double>>;
   
    class SplitStrategy{
    public:
        SplitStrategy() = default;
        SplitStrategy(std::vector<ValueRange> &input_ranges):input_ranges_(input_ranges){}
        
        enum class Status{
            STABLE,
            UNSTABLE,
            UNCERTERN,
        };
        
        std::vector<SplitStrategy> split() const;
        bool splitable();
        bool stabilize(std::set<llvm::Value *> &VSet, ValueRange &stableWN);
        
        double getMidCost() const{
            llvm::Value *V = target_as_.getPerturbationUpperBound().first;
            return mid_perturbation_map_.at(target_var_).at(V);
        }
        
        
        void setTarget(llvm::Value *V, const AbstractState &as){
            target_as_ = as;
            target_var_ = V;
        }
        
        Status getStatus() const{
            if(target_var_ == nullptr){
                return Status::UNCERTERN;
            }
//            double unitRoundoff;
//#ifdef SINGLE_FP_TYPE
//            unitRoundoff = std::numeric_limits<float>::epsilon();
//#else
//            unitRoundoff = std::numeric_limits<double>::epsilon();
//#endif
            ValueRange wn = target_as_.getWilkinsonNumber();
            if(wn.lower() > 1){
                return Status::UNSTABLE;
            }else if(wn.upper() <= 1){
                return Status::STABLE;
            }
            
            return Status::UNCERTERN;
        }
        
        const AbstractState& getTargetAbstractState(){
            return target_as_;
        }
        
        const ValueRange& getInputRange(int i) const{
            return input_ranges_[i];
        }
        
        void print(llvm::raw_ostream &out, llvm::PerturbationMap perturbation_map);
        
    private:
        std::vector<ValueRange> input_ranges_;
        unsigned split_dim_ = 0;
        
        AbstractState target_as_; //represent the abstract state of the return value
        llvm::Value* target_var_;
        
        MidPerturbationMap mid_perturbation_map_; //represent the perturbation at the mid point of input intervals
        //DiffArgMap diff_argument_map_;
        //SplitInfoState &split_state_;
        //llvm::Value *target_var_;
        
        double termination_epsilon = 0.000001; //TODO: set termination epsilon
        
        friend bool operator<(const SplitStrategy& lhs, const SplitStrategy& rhs);
    };
}

#endif /* SplitStrategy_h */
