//
//  SplitStrategy.cpp
//  LLVMAnnoInstCombine
//
//  Created by Gu Yijia on 3/12/18.
//

#include "SplitStrategy.h"

#include "llvm/Support/Format.h"

using namespace raic;
using namespace llvm;

void SplitStrategy::print(raw_ostream &out, PerturbationMap perturbation_map){
    outs() << "Input Region:" << "\n";
    int input_index = 0;
    for (auto i : input_ranges_){
        outs() << "[" << i.lower() << "," << i.upper() << "]\n";
        input_index ++;
    }
    if(target_var_ == nullptr){
        return;
    }
    outs() << "Value Range: " << "[" << target_as_.getValueRange().lower() << "," << target_as_.getValueRange().upper() << "]\n";
    
    ValueRange wn = target_as_.getWilkinsonNumber();
    ValueRange cn = target_as_.getConditionNumber();
    ValueRange tp = target_as_.getTotalPerturbation();
    
    outs() << "Wilkinson Number: " << "[" << wn.lower() << "," << wn.upper() << "]\n";
    outs() << "Condition Number: " << "[" << cn.lower() << "," << cn.upper() << "]\n";
    outs() << "Total Perturbation: " << "[" << tp.lower() << "," << tp.upper() << "]\n";
    
    outs() << "Perturbation Info:"<< "\n";
    for(auto i : target_as_.getDifferentialMap()){
        outs() << "[" << format("%.17f", i.second.lower()) <<","<< format("%.17f", i.second.upper())<<"]"
        << "\n";
    }
}

bool SplitStrategy::splitable(){
    if(boost::numeric::width(input_ranges_.at(split_dim_)) <= termination_epsilon){
        for(int i = 0; i < input_ranges_.size(); i ++){
            if(boost::numeric::width(input_ranges_[i]) > termination_epsilon){
                split_dim_ = i;
                return true;
            }
        }
        return false;
    }
    return true;
}

std::vector<SplitStrategy> SplitStrategy::split() const{
    std::vector<SplitStrategy> sv;
    SplitStrategy s1, s2;
    s1.input_ranges_ = input_ranges_;
    s2.input_ranges_ = input_ranges_;
    s1.input_ranges_[split_dim_] = ValueRange(input_ranges_[split_dim_].lower(), boost::numeric::median(input_ranges_[split_dim_]));
    s2.input_ranges_[split_dim_] = ValueRange(boost::numeric::median(input_ranges_[split_dim_]), input_ranges_[split_dim_].upper());
    sv.push_back(s1);
    sv.push_back(s2);
    return sv;
}

bool SplitStrategy::stabilize(std::set<llvm::Value *> &VSet, ValueRange &stableWN){
    ValueRange wn = target_as_.getWilkinsonNumber();
    if(wn.lower() < 1 && wn.upper() > 1){
        return false;
    }
    
    if(wn.upper() < 1){
        stableWN = boost::numeric::hull(stableWN, wn);
        return true;
    }
    
    std::vector<std::pair<Value*, ValueRange>> pairs;
    for (auto itr = target_as_.diff_with_deltas_.begin(); itr != target_as_.diff_with_deltas_.end(); ++itr){
        if(itr -> second.upper() < 0){
            pairs.push_back(std::make_pair(itr -> first,  ValueRange(abs(itr -> second.upper()), abs(itr -> second.lower()))));
        }else{
            pairs.push_back(*itr);
        }
    }
    
    sort(pairs.begin(), pairs.end(), [=](std::pair<Value*, ValueRange>& a, std::pair<Value*, ValueRange>& b)
    {
        return a.second.upper() < b.second.upper();
    }
    );
    
    int i = 1;
    ValueRange cd = target_as_.getConditionNumber();
    while(wn.upper() > 1){
        ValueRange totalPerturb = ValueRange(0);
        for(int j = 0; j < pairs.size() - i; j ++){
            totalPerturb += pairs[j].second;
        }
        wn = totalPerturb/cd;
        VSet.insert(pairs[pairs.size() - i].first);
        i ++;
    }
    boost::numeric::hull(stableWN, wn);
    return true;
}


bool raic::operator<(const SplitStrategy& lhs, const SplitStrategy& rhs){
    if(lhs.target_var_ == nullptr){ //handle the trivial case
        return false;
    }else if(rhs.target_var_ == nullptr){
        return true;
    }
    
    return lhs.target_as_.getWilkinsonNumber().upper() < rhs.target_as_.getWilkinsonNumber().upper();
}

