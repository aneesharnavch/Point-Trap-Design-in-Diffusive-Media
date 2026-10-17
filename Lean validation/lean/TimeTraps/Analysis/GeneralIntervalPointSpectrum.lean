module

public import TimeTraps.Analysis.GeneralIntervalPointOperator
public import TimeTraps.Analysis.CompactInverseDomainCharacterization

@[expose] public section

/-! The constructed complete L2 eigenbasis consists of actual H1 states
for the interval point-contact operator. Eigenvalues are positive reciprocals
of the compact inverse spectrum; their growth counts multiplicity. -/

namespace TimeTraps.Analysis

open Set Filter InnerProductSpace IntervalSobolevSpace
open scoped Topology

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

def IntervalPointProblem.eigenbasis (P : IntervalPointProblem ι l r) :
    HilbertBasis (CompactSpectralIndex P.inverse) ℝ (IntervalSobolevL2 l r) :=
  P.compactPositiveInverse.eigenbasis

def IntervalPointProblem.eigenstate (P : IntervalPointProblem ι l r) (i : CompactSpectralIndex P.inverse) :
    IntervalSobolevSpace l r := P.solution (i.1⁻¹ • P.eigenbasis i)

theorem IntervalPointProblem.eigenstate_state (P : IntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.inverse) : (P.eigenstate i).state = P.eigenbasis i := by
  change P.inverse (i.1⁻¹ • P.eigenbasis i) = P.eigenbasis i
  rw [map_smul]
  exact P.compactPositiveInverse.reciprocal_eigen i

theorem IntervalPointProblem.eigenvalue_positive (P : IntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.inverse) : 0 < i.1⁻¹ :=
  P.compactPositiveInverse.reciprocal_positive i

theorem IntervalPointProblem.eigenvalues_grow (P : IntervalPointProblem ι l r) :
    Tendsto (fun i : CompactSpectralIndex P.inverse => i.1⁻¹) cofinite atTop :=
  P.compactPositiveInverse.reciprocals_tendsto_atTop

theorem IntervalPointProblem.finite_eigenvalues_below (P : IntervalPointProblem ι l r) (R : ℝ) :
    {i : CompactSpectralIndex P.inverse | i.1⁻¹ ≤ R}.Finite :=
  P.compactPositiveInverse.finite_reciprocals_le R

theorem IntervalPointProblem.eigenbasis_operator_graph (P : IntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.inverse) :
    (P.eigenbasis i, i.1⁻¹ • P.eigenbasis i) ∈ P.operator.graph := by
  rw [P.operator_graph_iff, map_smul]
  exact P.compactPositiveInverse.reciprocal_eigen i

theorem IntervalPointProblem.eigenstate_weak (P : IntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.inverse) (v : IntervalSobolevSpace l r) :
    P.form (P.eigenstate i) v = i.1⁻¹ * inner ℝ (P.eigenstate i).state v.state := by
  rw [P.eigenstate_state]
  change P.form (P.solution (i.1⁻¹ • P.eigenbasis i)) v = _
  rw [P.solution_spec, real_inner_smul_left]

theorem IntervalPointProblem.eigenstate_physical_weak (P : IntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.inverse) (v : ℝ → ℝ) (hv : IntervalEnergy v l r) :
    intervalPointForm P.diffusivity P.strength P.site l r
      ((P.eigenstate i).representative P.interval_pos) v =
        i.1⁻¹ * ∫ x in l..r, (P.eigenstate i).representative P.interval_pos x * v x := by
  have he := P.eigenstate_weak i (ofEnergy hv P.interval_pos)
  change intervalSobolevPointForm P.interval_pos P.diffusivity P.strength P.site P.site_mem
    (P.eigenstate i) (ofEnergy hv P.interval_pos) = _ at he
  rw [intervalSobolevPointForm_apply, state_inner _ _ P.interval_pos] at he
  rw [intervalPointForm_congr P.diffusivity P.strength P.site P.interval_pos.le P.site_mem (fun _ _ => rfl)
    (representative_ofEnergy hv P.interval_pos)] at he
  calc
    _ = i.1⁻¹ * ∫ x in l..r, (P.eigenstate i).representative P.interval_pos x *
        (ofEnergy hv P.interval_pos).representative P.interval_pos x := he
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr_Ioo_of_le P.interval_pos.le
      intro x hx
      change (P.eigenstate i).representative P.interval_pos x *
        (ofEnergy hv P.interval_pos).representative P.interval_pos x =
        (P.eigenstate i).representative P.interval_pos x * v x
      rw [representative_ofEnergy hv P.interval_pos (Ioo_subset_Icc_self hx)]

theorem IntervalPointProblem.eigenbasis_expansion (P : IntervalPointProblem ι l r) (f : IntervalSobolevL2 l r) :
    HasSum (fun i : CompactSpectralIndex P.inverse =>
      inner ℝ (P.eigenbasis i) f • P.eigenbasis i) f :=
  P.compactPositiveInverse.hasSum_eigenbasis f

theorem IntervalPointProblem.operator_domain_spectral_iff (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) : f ∈ P.operator.domain ↔
      Summable (fun i : CompactSpectralIndex P.inverse =>
        (i.1⁻¹ * inner ℝ (P.eigenbasis i) f) ^ 2) :=
  P.compactPositiveInverse.mem_inverse_domain_iff f

theorem IntervalPointProblem.operator_expansion (P : IntervalPointProblem ι l r)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.inverse =>
      (i.1⁻¹ * inner ℝ (P.eigenbasis i) (f : IntervalSobolevL2 l r)) • P.eigenbasis i)
        (P.operator f) :=
  P.compactPositiveInverse.hasSum_inverse f

end

end TimeTraps.Analysis
