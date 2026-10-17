module

public import TimeTraps.Analysis.IntervalPeriodicEigenEquivalence
public import TimeTraps.Analysis.CompactInverseDomainCharacterization

@[expose] public section

/-! The constructed complete L2 eigenbasis consists of actual H1 states
for the periodic point-contact operator. Eigenvalues are positive reciprocals
of the compact inverse spectrum; their growth counts multiplicity. -/

namespace TimeTraps.Analysis

open Set Filter InnerProductSpace IntervalSobolevSpace
open scoped Topology

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

def PeriodicPointProblem.eigenbasis (P : PeriodicPointProblem ι l r) :
    HilbertBasis (CompactSpectralIndex P.inverse) ℝ (IntervalSobolevL2 l r) :=
  P.compactPositiveInverse.eigenbasis

def PeriodicPointProblem.eigenstate (P : PeriodicPointProblem ι l r) (i : CompactSpectralIndex P.inverse) :
    IntervalPeriodicSpace P.boundary := P.solution (i.1⁻¹ • P.eigenbasis i)

theorem PeriodicPointProblem.eigenstate_state (P : PeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.inverse) : (P.boundary.stateL (P.eigenstate i)) = P.eigenbasis i := by
  change P.inverse (i.1⁻¹ • P.eigenbasis i) = P.eigenbasis i
  rw [map_smul]
  exact P.compactPositiveInverse.reciprocal_eigen i

theorem PeriodicPointProblem.eigenvalue_positive (P : PeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.inverse) : 0 < i.1⁻¹ :=
  P.compactPositiveInverse.reciprocal_positive i

theorem PeriodicPointProblem.eigenvalues_grow (P : PeriodicPointProblem ι l r) :
    Tendsto (fun i : CompactSpectralIndex P.inverse => i.1⁻¹) cofinite atTop :=
  P.compactPositiveInverse.reciprocals_tendsto_atTop

theorem PeriodicPointProblem.finite_eigenvalues_below (P : PeriodicPointProblem ι l r) (R : ℝ) :
    {i : CompactSpectralIndex P.inverse | i.1⁻¹ ≤ R}.Finite :=
  P.compactPositiveInverse.finite_reciprocals_le R

theorem PeriodicPointProblem.eigenbasis_operator_graph (P : PeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.inverse) :
    (P.eigenbasis i, i.1⁻¹ • P.eigenbasis i) ∈ P.operator.graph := by
  rw [P.operator_graph_iff, map_smul]
  exact P.compactPositiveInverse.reciprocal_eigen i

theorem PeriodicPointProblem.eigenstate_weak (P : PeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.inverse) (v : IntervalPeriodicSpace P.boundary) :
    P.form (P.eigenstate i) v = i.1⁻¹ * inner ℝ (P.boundary.stateL (P.eigenstate i)) (P.boundary.stateL v) := by
  rw [P.eigenstate_state]
  change P.form (P.solution (i.1⁻¹ • P.eigenbasis i)) v = _
  rw [P.solution_spec, real_inner_smul_left]

theorem PeriodicPointProblem.eigenstate_physical_weak (P : PeriodicPointProblem ι l r)
    (i : CompactSpectralIndex P.inverse) (v : ℝ → ℝ) (hv : IntervalEnergy v l r)
    (hvp : v l = v r) :
    intervalPointForm P.diffusivity P.strength P.site l r
      ((P.eigenstate i).val.representative P.boundary.interval_pos) v =
        i.1⁻¹ * ∫ x in l..r, (P.eigenstate i).val.representative P.boundary.interval_pos x * v x :=
  (P.hilbert_eigen_iff_physical (P.eigenstate i) i.1⁻¹).mp (P.eigenstate_weak i) v hv hvp

theorem PeriodicPointProblem.eigenbasis_expansion (P : PeriodicPointProblem ι l r) (f : IntervalSobolevL2 l r) :
    HasSum (fun i : CompactSpectralIndex P.inverse =>
      inner ℝ (P.eigenbasis i) f • P.eigenbasis i) f :=
  P.compactPositiveInverse.hasSum_eigenbasis f

theorem PeriodicPointProblem.operator_domain_spectral_iff (P : PeriodicPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : f ∈ P.operator.domain ↔
      Summable (fun i : CompactSpectralIndex P.inverse =>
        (i.1⁻¹ * inner ℝ (P.eigenbasis i) f) ^ 2) :=
  P.compactPositiveInverse.mem_inverse_domain_iff f

theorem PeriodicPointProblem.operator_expansion (P : PeriodicPointProblem ι l r)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.inverse =>
      (i.1⁻¹ * inner ℝ (P.eigenbasis i) (f : IntervalSobolevL2 l r)) • P.eigenbasis i)
        (P.operator f) :=
  P.compactPositiveInverse.hasSum_inverse f

end

end TimeTraps.Analysis
