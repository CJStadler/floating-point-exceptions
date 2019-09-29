//
//  AbstractState.cpp
//  LLVMCertInstCombine
//
//  Created by Gu Yijia on 12/22/17.
//

#include "AbstractState.h"

#include "llvm/Support/Format.h"

using namespace raic;
using namespace llvm;
using namespace std;

raw_ostream &raic::operator<<(raw_ostream &out, const AbstractState &as){
    out << "Value Range ["
    <<  format("%.17f",as.value_range_.lower()) << "," << format("%.17f",as.value_range_.upper())
    << "]\n";
    out << "Delta Info" << "\n";
    double maxAbs = 0;
    for(auto i : as.diff_with_deltas_){
        maxAbs += max(abs(i.second.lower()), abs(i.second.upper()));
        out << "Relative Perturbation" << "[" << format("%.17f", i.second.lower()) <<","<< format("%.17f", i.second.upper())<<"]"
        <<"\n";
    }
    out << "Total Perturbation" << format("%.17f", maxAbs) << "\n";
#ifdef SINGLE_FP_TYPE
    ValueRange t = as.value_range_ * maxAbs * (double)numeric_limits<float>::epsilon();
    out << "ULP" << format("%.17f", as.value_range_.lower() * (double)numeric_limits<float>::epsilon()) << "\n";
#else
    ValueRange t = as.value_range_ * maxAbs * numeric_limits<double>::epsilon();
    out << "ULP" << format("%.17f", as.value_range_.lower() * numeric_limits<double>::epsilon()) << "\n";
#endif
    
    out << " Absolute Perturbation: [" << format("%.17f", t.lower()) << "," << format("%.17f", t.upper())
    << "]\n";
    return out;
}

void AbstractState::chainDiffMap(const ValueRange &coeff, const AbstractState *op){
    for(auto i : op->diff_with_deltas_){
        addDiff(coeff * i.second, i.first);
    }
}

void AbstractState::chainConditionMap(const ValueRange &coeff, const AbstractState *op){
    for(auto i : op -> condition_map_){
        addCondition(coeff * i.second, i.first);
    }
}

std::pair<llvm::Value *, ValueRange>  AbstractState::getPerturbationUpperBound() const{
    if(diff_with_deltas_.empty()){
        return pair<llvm::Value *, ValueRange>(nullptr, ValueRange(std::numeric_limits<double>::max(), std::numeric_limits<double>::max()));
    }
    
    pair<llvm::Value *, ValueRange> p;
    double ub = 0;
    for(auto i : diff_with_deltas_){
        if(boost::numeric::width(i.second) > ub){
            ub = boost::numeric::width(i.second);
            p = i;
        }
//        if(i.second.upper() > ub){
//            ub = i.second.upper();
//            p = i;
//        }
    }
    return p;
}

ValueRange AbstractState::getTotalPerturbation() const{
    ValueRange r = ValueRange(0);
    
    for(auto i : diff_with_deltas_){
        //assert(i.second.lower() * i.second.upper() >= 0 && "Violate subnormal assumption");
        if(i.second.upper() < 0){
            r += ValueRange(abs(i.second.upper()), abs(i.second.lower()));
        }else{
           r += i.second;
        }
    }
    
    return r;
}

ValueRange AbstractState::getConditionNumber() const{
    ValueRange r = ValueRange(0);
    for(auto i : condition_map_){
        assert(i.second.lower() * i.second.upper() >= 0 && "Violate subnormal assumption");
        if(i.second.upper() < 0){
            r += ValueRange(abs(i.second.upper()), abs(i.second.lower()));
        }else{
            r += i.second;
        }
    }
    if(r.upper() != 0 && r.upper() < 1){
        return ValueRange(1);
    }
    return r;
}


bool AbstractState::isPerturbationPrecise() const{
    if(diff_with_deltas_.empty()){
        return false;
    }

    bool isReproducible = true;
    for(auto i : diff_with_deltas_){
        if(boost::numeric::subset(i.second, ValueRange(-1, 1))){
            continue;
        } else if (!boost::numeric::overlap(i.second, ValueRange(-1, 1))){
            return true;
        } else {
            isReproducible = false;
        }
        
    }
//        assert(i.second.lower() > 0 && "Perturbation should always be > 0");
//        if(i.second.upper() > ub){
//            ub = i.second.upper();
//            p = i;
//        }
//    }
//    return std::floor(p.second.upper()) - std::floor(p.second.lower()) < 1;
    return isReproducible;
}

