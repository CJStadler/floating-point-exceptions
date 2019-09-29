//
//  AbstractState.h
//  Project
//
//  Created by Gu Yijia on 12/22/17.
//

#ifndef AbstractState_h
#define AbstractState_h

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instruction.h"

#include <vector>
#include <map>
#include <limits>
#include <boost/numeric/interval.hpp>

namespace raic{
    using ValueRange = boost::numeric::interval<double,
    boost::numeric::interval_lib::policies<boost::numeric::interval_lib::save_state<boost::numeric::interval_lib::rounded_transc_std<double> >,
    boost::numeric::interval_lib::checking_base<double> > >;
    
    struct Value_CMP
    {
        bool operator()(llvm::Value *p1, llvm::Value *p2) const{
            return p1 < p2 ;
        }
    };
    
    using DifferentialMap = std::map<llvm::Value *, ValueRange>;
    
    /// Class to represent the abstract value
    class AbstractState {
    public:
        std::pair<llvm::Value *, ValueRange> getPerturbationUpperBound() const;
        bool isPerturbationPrecise() const;
        
        ValueRange getTotalPerturbation() const;
        ValueRange getConditionNumber() const;
        ValueRange getWilkinsonNumber() const{
            return getTotalPerturbation()/getConditionNumber();
        }
        
        void chainDiffMap(const ValueRange &coeff, const AbstractState *op);
        void chainConditionMap(const ValueRange &coeff, const AbstractState *op);
        
        void addDiff(const ValueRange &logDiff, llvm::Value *V){
            if(diff_with_deltas_.find(V) == diff_with_deltas_.end()){
                diff_with_deltas_[V] = logDiff;
            }else{
                diff_with_deltas_[V] += logDiff;
            }
        }
        
        void addCondition(const ValueRange &logDiff, llvm::Value *V){
            if(condition_map_.find(V) == condition_map_.end()){
                condition_map_[V] = logDiff;
            }else{
                condition_map_[V] += logDiff;
            }
        }
        void clearState(){
            diff_with_deltas_.clear();
            condition_map_.clear();
        }

        
        const DifferentialMap& getDifferentialMap() const{
            return diff_with_deltas_;
        }
        
        const DifferentialMap& getConditionMap() const{
            return condition_map_;
        }
        
        void setValueRange(const double c1, const double c2){
            assert(!(boost::numeric::in(std::numeric_limits<double>::min(), ValueRange(c1, c2)) ||
                     boost::numeric::in(std::numeric_limits<double>::min(), ValueRange(-c2, -c1)))
                   && "Violate no underflow assumption");
            value_range_ = ValueRange(c1, c2);
        }
        
        void setValueRange(const ValueRange &v){
//            assert(!(boost::numeric::in(std::numeric_limits<double>::min(), v)||
//                     boost::numeric::in(std::numeric_limits<double>::min(), ValueRange(-v.upper(), -v.lower())))
//                   && "Violate no underflow assumption");
            value_range_ = v;
        }
        
        ValueRange getValueRange() const {
            return value_range_;
        }
        
        DifferentialMap diff_with_deltas_;  //!< differentials of the node with respect to delta
        DifferentialMap condition_map_;  //!< condition number of the function
       
        ValueRange value_range_; //!< possible range of the value of the node
        
        friend llvm::raw_ostream &operator<<(llvm::raw_ostream &out, const AbstractState &as);
    };
}
#endif /* AbstractState_h */
