// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

namespace opensmt {
%ignore InterpolationContext::InterpolationContext (SMTConfig &c, Theory &th, TermMapper &termMapper, ResolutionProof const &t, PartitionManager &pmanager);
%ignore InterpolationContext::printProofDotty ();
%ignore InterpolationContext::getInterpolants (const std::vector< vec< int > > &partitions, vec< PTRef > &interpolants);
%ignore InterpolationContext::getSingleInterpolant (vec< PTRef > &interpolants, const ipartitions_t &A_mask);
%ignore InterpolationContext::getSingleInterpolant (std::vector< PTRef > &interpolants, const ipartitions_t &A_mask);
%ignore InterpolationContext::getPathInterpolants (vec< PTRef > &interpolants, const std::vector< ipartitions_t > &A_masks);
%extend InterpolationContext  {
  PTRef getSingleInterpolant (const std::vector<int>& partition) {
    std::vector<PTRef> interpolants;
    ipartitions_t mask;
    for(int i : partition)
      opensmt::setbit(mask, i);
    $self->getSingleInterpolant(interpolants, mask);
    return interpolants[0];
  }

  %newobject getPathInterpolant;
  std::vector<PTRef> getPathInterpolants (const std::vector<std::vector<int>>& partitions) {
    vec<PTRef> interpolants;
    std::vector<ipartitions_t> masks;
    for(const std::vector<int>& partition : partitions) {
      ipartitions_t mask;
      for (int i : partition)
        opensmt::setbit(mask, i);
      masks.emplace_back(mask);
    }
    $self->getPathInterpolants(interpolants, masks);
    std::vector<PTRef> result;
    for (int i = 0; i < interpolants.size(); i++)
      result.emplace_back(interpolants[i]);
    return result;
 }
}
}

%include "include/opensmt/proof/InterpolationContext.h"
