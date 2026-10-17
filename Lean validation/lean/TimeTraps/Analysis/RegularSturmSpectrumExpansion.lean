module

public import TimeTraps.Analysis.RegularSturmSpectrum

@[expose] public section

/-! Complete unconditional expansions for the actual original regular
separated-boundary Sturm operator. The exact domain uses the squares of original
shifted-back eigenvalues, which may be negative or zero. -/

namespace TimeTraps.Analysis

open Set Filter InnerProductSpace IntervalSobolevSpace
open scoped Topology

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

theorem RegularSturmProblem.eigenbasis_expansion (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) :
    HasSum (fun i : CompactSpectralIndex P.shiftedInverse =>
      inner ℝ (P.eigenbasis i) f • P.eigenbasis i) f :=
  P.shiftedCompactPositiveInverse.hasSum_eigenbasis f

theorem RegularSturmProblem.eigenbasis_parseval (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) :
    HasSum (fun i : CompactSpectralIndex P.shiftedInverse =>
      (inner ℝ (P.eigenbasis i) f) ^ 2) (‖f‖ ^ 2) :=
  P.shiftedCompactPositiveInverse.hasSum_parseval f

theorem RegularSturmProblem.operator_domain_spectral_iff (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) : f ∈ P.operator.domain ↔
      Summable (fun i : CompactSpectralIndex P.shiftedInverse =>
        ((i.1⁻¹ - P.massShift) * inner ℝ (P.eigenbasis i) f) ^ 2) :=
  P.shiftedCompactPositiveInverse.mem_translated_domain_iff P.massShift f

theorem RegularSturmProblem.operator_expansion (P : RegularSturmProblem ι l r)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.shiftedInverse =>
      ((i.1⁻¹ - P.massShift) * inner ℝ (P.eigenbasis i) (f : IntervalSobolevL2 l r)) •
        P.eigenbasis i) (P.operator f) :=
  P.shiftedCompactPositiveInverse.hasSum_translated P.massShift f

theorem RegularSturmProblem.operator_norm_expansion (P : RegularSturmProblem ι l r)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.shiftedInverse =>
      ((i.1⁻¹ - P.massShift) * inner ℝ (P.eigenbasis i) (f : IntervalSobolevL2 l r)) ^ 2)
        (‖P.operator f‖ ^ 2) :=
  P.shiftedCompactPositiveInverse.hasSum_translated_norm P.massShift f

theorem RegularSturmProblem.operator_quadratic_expansion (P : RegularSturmProblem ι l r)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.shiftedInverse =>
      (i.1⁻¹ - P.massShift) * (inner ℝ (P.eigenbasis i) (f : IntervalSobolevL2 l r)) ^ 2)
        (inner ℝ (f : IntervalSobolevL2 l r) (P.operator f)) :=
  P.shiftedCompactPositiveInverse.hasSum_translated_quadratic P.massShift f

theorem RegularSturmProblem.operator_eigenvalue_index (P : RegularSturmProblem ι l r)
    {f : IntervalSobolevL2 l r} (hf : f ≠ 0) {ev : ℝ}
    (he : (f, ev • f) ∈ P.operator.graph) :
    ∃ i : CompactSpectralIndex P.shiftedInverse, i.1⁻¹ - P.massShift = ev :=
  P.shiftedCompactPositiveInverse.translated_eigenvalue_index P.massShift hf he

end

end TimeTraps.Analysis
