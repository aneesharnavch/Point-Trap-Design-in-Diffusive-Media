module

public import TimeTraps.Analysis.SignedPeriodicPointSpectrumEquivalence
public import TimeTraps.Analysis.ShiftedInverseSpectrumDomain
public import TimeTraps.Analysis.ShiftedInverseSpectrumEnumeration

@[expose] public section

/-! The complete eigenbasis of the actual original signed periodic
operator consists of physical endpoint-matched periodic H1 states. Eigenvalues are
reciprocals of the shifted inverse values minus the explicit mass shift;
negative and zero eigenvalues are allowed. -/

namespace TimeTraps.Analysis

open Set Filter InnerProductSpace IntervalSobolevSpace
open scoped Topology

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

def SignedPeriodicPointProblem.eigenbasis (P : SignedPeriodicPointProblem ι l r) :
    HilbertBasis (CompactSpectralIndex P.shiftedInverse) ℝ (IntervalSobolevL2 l r) :=
  P.shiftedCompactPositiveInverse.eigenbasis

def SignedPeriodicPointProblem.eigenstate (P : SignedPeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) : IntervalPeriodicSpace P.boundary :=
  P.shiftedSolution (i.1⁻¹ • P.eigenbasis i)

theorem SignedPeriodicPointProblem.eigenstate_state (P : SignedPeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) : P.boundary.stateL (P.eigenstate i) = P.eigenbasis i := by
  change P.shiftedInverse (i.1⁻¹ • P.eigenbasis i) = P.eigenbasis i
  rw [map_smul]
  exact P.shiftedCompactPositiveInverse.reciprocal_eigen i

theorem SignedPeriodicPointProblem.eigenstate_periodic (P : SignedPeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) :
    (P.eigenstate i).val.representative P.boundary.interval_pos l =
      (P.eigenstate i).val.representative P.boundary.interval_pos r :=
  (P.boundary.representative_periodic (P.eigenstate i)).symm

theorem SignedPeriodicPointProblem.eigenbasis_operator_graph (P : SignedPeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) :
    (P.eigenbasis i, (i.1⁻¹ - P.massShift) • P.eigenbasis i) ∈ P.operator.graph :=
  P.shiftedCompactPositiveInverse.translated_eigenbasis_graph P.massShift i

theorem SignedPeriodicPointProblem.eigenstate_weak (P : SignedPeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) (v : IntervalPeriodicSpace P.boundary) :
    P.form (P.eigenstate i) v = (i.1⁻¹ - P.massShift) *
      inner ℝ (P.boundary.stateL (P.eigenstate i)) (P.boundary.stateL v) := by
  apply (P.operator_eigen_iff_hilbert (P.eigenstate i) (i.1⁻¹ - P.massShift)).mp _ v
  rw [P.eigenstate_state]
  exact P.eigenbasis_operator_graph i

theorem SignedPeriodicPointProblem.eigenstate_physical_weak (P : SignedPeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) (v : ℝ → ℝ) (hv : IntervalEnergy v l r)
    (hvz : v l = v r) :
    intervalPointForm P.diffusivity P.strength P.site l r
      ((P.eigenstate i).val.representative P.boundary.interval_pos) v =
        (i.1⁻¹ - P.massShift) * ∫ x in l..r,
          (P.eigenstate i).val.representative P.boundary.interval_pos x * v x :=
  (P.hilbert_eigen_iff_physical (P.eigenstate i) (i.1⁻¹ - P.massShift)).mp
    (P.eigenstate_weak i) v hv hvz

theorem SignedPeriodicPointProblem.eigenvalue_lower (P : SignedPeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) :
    -intervalPointNegativeBound P.diffusivity P.strength l r ≤ i.1⁻¹ - P.massShift := by
  have h := P.form_semibounded (P.eigenstate i)
  rw [P.eigenstate_weak, P.eigenstate_state, real_inner_self_eq_norm_sq,
    P.eigenbasis.orthonormal.norm_eq_one i] at h
  simpa only [one_pow, mul_one] using h

theorem SignedPeriodicPointProblem.eigenvalues_grow (P : SignedPeriodicPointProblem ι l r) :
    Tendsto (fun i : CompactSpectralIndex P.shiftedInverse => i.1⁻¹ - P.massShift) cofinite atTop :=
  P.shiftedCompactPositiveInverse.translated_eigenvalues_tendsto_atTop P.massShift

theorem SignedPeriodicPointProblem.finite_eigenvalues_below (P : SignedPeriodicPointProblem ι l r)
    (R : ℝ) : {i : CompactSpectralIndex P.shiftedInverse | i.1⁻¹ - P.massShift ≤ R}.Finite :=
  P.shiftedCompactPositiveInverse.finite_translated_eigenvalues_le P.massShift R

end

end TimeTraps.Analysis
