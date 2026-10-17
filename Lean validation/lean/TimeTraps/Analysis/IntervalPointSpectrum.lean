module

public import TimeTraps.Analysis.IntervalPointOperator
public import TimeTraps.Analysis.CompactInverseDomainCharacterization

@[expose] public section

/-! The constructed complete L2 eigenbasis consists of actual H1 states
for the interval point-contact operator. Eigenvalues are positive reciprocals
of the compact inverse spectrum; their growth counts multiplicity. -/

namespace TimeTraps.Analysis

open Set Filter InnerProductSpace IntervalSobolevSpace
open scoped Topology

variable {ι : Type*} [Fintype ι]

noncomputable section

def UnitPointProblem.eigenbasis (P : UnitPointProblem ι) :
    HilbertBasis (CompactSpectralIndex P.inverse) ℝ UnitIntervalL2 :=
  P.compactPositiveInverse.eigenbasis

def UnitPointProblem.eigenstate (P : UnitPointProblem ι) (i : CompactSpectralIndex P.inverse) :
    UnitIntervalSobolev := P.solution (i.1⁻¹ • P.eigenbasis i)

theorem UnitPointProblem.eigenstate_state (P : UnitPointProblem ι)
    (i : CompactSpectralIndex P.inverse) : (P.eigenstate i).state = P.eigenbasis i := by
  change P.inverse (i.1⁻¹ • P.eigenbasis i) = P.eigenbasis i
  rw [map_smul]
  exact P.compactPositiveInverse.reciprocal_eigen i

theorem UnitPointProblem.eigenvalue_positive (P : UnitPointProblem ι)
    (i : CompactSpectralIndex P.inverse) : 0 < i.1⁻¹ :=
  P.compactPositiveInverse.reciprocal_positive i

theorem UnitPointProblem.eigenvalues_grow (P : UnitPointProblem ι) :
    Tendsto (fun i : CompactSpectralIndex P.inverse => i.1⁻¹) cofinite atTop :=
  P.compactPositiveInverse.reciprocals_tendsto_atTop

theorem UnitPointProblem.finite_eigenvalues_below (P : UnitPointProblem ι) (R : ℝ) :
    {i : CompactSpectralIndex P.inverse | i.1⁻¹ ≤ R}.Finite :=
  P.compactPositiveInverse.finite_reciprocals_le R

theorem UnitPointProblem.eigenbasis_operator_graph (P : UnitPointProblem ι)
    (i : CompactSpectralIndex P.inverse) :
    (P.eigenbasis i, i.1⁻¹ • P.eigenbasis i) ∈ P.operator.graph := by
  rw [P.operator_graph_iff, map_smul]
  exact P.compactPositiveInverse.reciprocal_eigen i

theorem UnitPointProblem.eigenstate_weak (P : UnitPointProblem ι)
    (i : CompactSpectralIndex P.inverse) (v : UnitIntervalSobolev) :
    P.form (P.eigenstate i) v = i.1⁻¹ * inner ℝ (P.eigenstate i).state v.state := by
  rw [P.eigenstate_state]
  change P.form (P.solution (i.1⁻¹ • P.eigenbasis i)) v = _
  rw [P.solution_spec, real_inner_smul_left]

theorem UnitPointProblem.eigenstate_physical_weak (P : UnitPointProblem ι)
    (i : CompactSpectralIndex P.inverse) (v : ℝ → ℝ) (hv : IntervalEnergy v 0 1) :
    unitPointForm P.diffusivity P.strength P.site
      ((P.eigenstate i).representative zero_lt_one) v =
        i.1⁻¹ * ∫ x in (0 : ℝ)..1, (P.eigenstate i).representative zero_lt_one x * v x := by
  have he := P.eigenstate_weak i (ofEnergy hv zero_lt_one)
  change unitSobolevForm P.diffusivity P.strength P.site P.site_mem
    (P.eigenstate i) (ofEnergy hv zero_lt_one) = _ at he
  rw [unitSobolevForm_apply, state_inner _ _ zero_lt_one] at he
  rw [unitPointForm_congr P.diffusivity P.strength P.site P.site_mem (fun _ _ => rfl)
    (representative_ofEnergy hv zero_lt_one)] at he
  calc
    _ = i.1⁻¹ * ∫ x in (0 : ℝ)..1, (P.eigenstate i).representative zero_lt_one x *
        (ofEnergy hv zero_lt_one).representative zero_lt_one x := he
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro x hx
      change (P.eigenstate i).representative zero_lt_one x *
        (ofEnergy hv zero_lt_one).representative zero_lt_one x =
        (P.eigenstate i).representative zero_lt_one x * v x
      rw [representative_ofEnergy hv zero_lt_one (Ioo_subset_Icc_self hx)]

theorem UnitPointProblem.eigenbasis_expansion (P : UnitPointProblem ι) (f : UnitIntervalL2) :
    HasSum (fun i : CompactSpectralIndex P.inverse =>
      inner ℝ (P.eigenbasis i) f • P.eigenbasis i) f :=
  P.compactPositiveInverse.hasSum_eigenbasis f

theorem UnitPointProblem.operator_domain_spectral_iff (P : UnitPointProblem ι)
    (f : UnitIntervalL2) : f ∈ P.operator.domain ↔
      Summable (fun i : CompactSpectralIndex P.inverse =>
        (i.1⁻¹ * inner ℝ (P.eigenbasis i) f) ^ 2) :=
  P.compactPositiveInverse.mem_inverse_domain_iff f

theorem UnitPointProblem.operator_expansion (P : UnitPointProblem ι)
    (f : P.operator.domain) :
    HasSum (fun i : CompactSpectralIndex P.inverse =>
      (i.1⁻¹ * inner ℝ (P.eigenbasis i) (f : UnitIntervalL2)) • P.eigenbasis i)
        (P.operator f) :=
  P.compactPositiveInverse.hasSum_inverse f

end

end TimeTraps.Analysis
