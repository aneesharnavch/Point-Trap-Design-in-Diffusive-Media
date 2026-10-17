module

public import TimeTraps.Analysis.SignedIntervalPointEigenEquivalence
public import TimeTraps.Analysis.ShiftedInverseSpectrumDomain
public import TimeTraps.Analysis.ShiftedInverseSpectrumEnumeration

@[expose] public section

/-! The complete spectrum of the actual unshifted signed interval operator.
The Hilbert eigenvectors are represented by actual H1 states. Eigenvalues
are reciprocal shifted-inverse values minus the explicit mass shift; they
are bounded below, with zero and negative values allowed. -/

namespace TimeTraps.Analysis

open Set Filter InnerProductSpace IntervalSobolevSpace
open scoped Topology

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

def SignedIntervalPointProblem.eigenbasis (P : SignedIntervalPointProblem ι l r) :
    HilbertBasis (CompactSpectralIndex P.shiftedInverse) ℝ (IntervalSobolevL2 l r) :=
  P.shiftedCompactPositiveInverse.eigenbasis

def SignedIntervalPointProblem.eigenstate (P : SignedIntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) : IntervalSobolevSpace l r :=
  P.shiftedSolution (i.1⁻¹ • P.eigenbasis i)

theorem SignedIntervalPointProblem.eigenstate_state (P : SignedIntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) : (P.eigenstate i).state = P.eigenbasis i := by
  change P.shiftedInverse (i.1⁻¹ • P.eigenbasis i) = P.eigenbasis i
  rw [map_smul]
  exact P.shiftedCompactPositiveInverse.reciprocal_eigen i

theorem SignedIntervalPointProblem.eigenbasis_operator_graph (P : SignedIntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) :
    (P.eigenbasis i, (i.1⁻¹ - P.massShift) • P.eigenbasis i) ∈ P.operator.graph :=
  P.shiftedCompactPositiveInverse.translated_eigenbasis_graph P.massShift i

theorem SignedIntervalPointProblem.eigenstate_weak (P : SignedIntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) (v : IntervalSobolevSpace l r) :
    P.form (P.eigenstate i) v =
      (i.1⁻¹ - P.massShift) * inner ℝ (P.eigenstate i).state v.state := by
  apply (P.operator_eigen_iff_hilbert (P.eigenstate i) (i.1⁻¹ - P.massShift)).mp _ v
  rw [P.eigenstate_state]
  exact P.eigenbasis_operator_graph i

theorem SignedIntervalPointProblem.eigenstate_physical_weak (P : SignedIntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) (v : ℝ → ℝ) (hv : IntervalEnergy v l r) :
    intervalPointForm P.diffusivity P.strength P.site l r
      ((P.eigenstate i).representative P.interval_pos) v =
        (i.1⁻¹ - P.massShift) * ∫ x in l..r,
          (P.eigenstate i).representative P.interval_pos x * v x :=
  (P.hilbert_eigen_iff_physical (P.eigenstate i) (i.1⁻¹ - P.massShift)).mp
    (P.eigenstate_weak i) v hv

theorem SignedIntervalPointProblem.eigenvalue_lower (P : SignedIntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) :
    -intervalPointNegativeBound P.diffusivity P.strength l r ≤ i.1⁻¹ - P.massShift := by
  have h := P.form_semibounded (P.eigenstate i)
  rw [P.eigenstate_weak, P.eigenstate_state, real_inner_self_eq_norm_sq,
    P.eigenbasis.orthonormal.norm_eq_one i] at h
  simpa only [one_pow, mul_one] using h

theorem SignedIntervalPointProblem.eigenvalues_grow (P : SignedIntervalPointProblem ι l r) :
    Tendsto (fun i : CompactSpectralIndex P.shiftedInverse => i.1⁻¹ - P.massShift) cofinite atTop :=
  P.shiftedCompactPositiveInverse.translated_eigenvalues_tendsto_atTop P.massShift

theorem SignedIntervalPointProblem.finite_eigenvalues_below (P : SignedIntervalPointProblem ι l r)
    (R : ℝ) : {i : CompactSpectralIndex P.shiftedInverse | i.1⁻¹ - P.massShift ≤ R}.Finite :=
  P.shiftedCompactPositiveInverse.finite_translated_eigenvalues_le P.massShift R

theorem SignedIntervalPointProblem.eigenbasis_expansion (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) :
    HasSum (fun i : CompactSpectralIndex P.shiftedInverse =>
      inner ℝ (P.eigenbasis i) f • P.eigenbasis i) f :=
  P.shiftedCompactPositiveInverse.hasSum_eigenbasis f

theorem SignedIntervalPointProblem.eigenbasis_parseval (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) :
    HasSum (fun i : CompactSpectralIndex P.shiftedInverse =>
      (inner ℝ (P.eigenbasis i) f) ^ 2) (‖f‖ ^ 2) :=
  P.shiftedCompactPositiveInverse.hasSum_parseval f

theorem SignedIntervalPointProblem.operator_domain_spectral_iff (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : f ∈ P.operator.domain ↔
      Summable (fun i : CompactSpectralIndex P.shiftedInverse =>
        ((i.1⁻¹ - P.massShift) * inner ℝ (P.eigenbasis i) f) ^ 2) :=
  P.shiftedCompactPositiveInverse.mem_translated_domain_iff P.massShift f

theorem SignedIntervalPointProblem.operator_expansion (P : SignedIntervalPointProblem ι l r)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.shiftedInverse =>
      ((i.1⁻¹ - P.massShift) * inner ℝ (P.eigenbasis i) (f : IntervalSobolevL2 l r)) •
        P.eigenbasis i) (P.operator f) :=
  P.shiftedCompactPositiveInverse.hasSum_translated P.massShift f

theorem SignedIntervalPointProblem.operator_norm_expansion (P : SignedIntervalPointProblem ι l r)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.shiftedInverse =>
      ((i.1⁻¹ - P.massShift) * inner ℝ (P.eigenbasis i) (f : IntervalSobolevL2 l r)) ^ 2)
        (‖P.operator f‖ ^ 2) :=
  P.shiftedCompactPositiveInverse.hasSum_translated_norm P.massShift f

theorem SignedIntervalPointProblem.operator_quadratic_expansion (P : SignedIntervalPointProblem ι l r)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.shiftedInverse =>
      (i.1⁻¹ - P.massShift) * (inner ℝ (P.eigenbasis i) (f : IntervalSobolevL2 l r)) ^ 2)
        (inner ℝ (f : IntervalSobolevL2 l r) (P.operator f)) :=
  P.shiftedCompactPositiveInverse.hasSum_translated_quadratic P.massShift f

theorem SignedIntervalPointProblem.operator_eigenvalue_index (P : SignedIntervalPointProblem ι l r)
    {f : IntervalSobolevL2 l r} (hf : f ≠ 0) {ev : ℝ}
    (he : (f, ev • f) ∈ P.operator.graph) :
    ∃ i : CompactSpectralIndex P.shiftedInverse, i.1⁻¹ - P.massShift = ev :=
  P.shiftedCompactPositiveInverse.translated_eigenvalue_index P.massShift hf he

end

end TimeTraps.Analysis
