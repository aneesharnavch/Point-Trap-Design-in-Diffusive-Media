module

public import TimeTraps.Analysis.SignedIntervalPointGroundSimplicityHilbert
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

/-! Simplicity of the actual unbounded signed operator at its principal
value. The eigenspace is defined by its actual graph in the original L2
Hilbert space, and its dimension one is derived from weak-state uniqueness. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.principal_operator_scalar
    (P : SignedIntervalPointProblem ι l r) {u v : IntervalSobolevL2 l r}
    (hu₀ : u ≠ 0) (hu : (u, P.principalValue • u) ∈ P.operator.graph)
    (hv : (v, P.principalValue • v) ∈ P.operator.graph) :
    ∃ c : ℝ, v = c • u := by
  obtain ⟨U, hU, heU⟩ := (P.operator_graph_iff_hilbert _ _).mp hu
  obtain ⟨V, hV, heV⟩ := (P.operator_graph_iff_hilbert _ _).mp hv
  have hEU : ∀ w : IntervalSobolevSpace l r,
      P.form U w = P.principalValue * inner ℝ U.state w.state := by
    intro w
    rw [heU w, real_inner_smul_left, hU]
  have hEV : ∀ w : IntervalSobolevSpace l r,
      P.form V w = P.principalValue * inner ℝ V.state w.state := by
    intro w
    rw [heV w, real_inner_smul_left, hV]
  have hU₀ : U.representative P.interval_pos l ≠ 0 := by
    intro hz
    have hzero := P.principal_hilbert_zero_of_left_trace U hEU hz
    apply hu₀
    rw [← hU, hzero]
    rfl
  let c := V.representative P.interval_pos l / U.representative P.interval_pos l
  have he : V = c • U := P.principal_hilbert_scalar U V hU₀ hEU hEV
  refine ⟨c, ?_⟩
  calc
    v = V.state := hV.symm
    _ = c • U.state := by
      rw [he]
      exact (stateL l r).map_smul c U
    _ = c • u := by rw [hU]

noncomputable def SignedIntervalPointProblem.principalEigenspace
    (P : SignedIntervalPointProblem ι l r) : Submodule ℝ (IntervalSobolevL2 l r) :=
  P.operator.graph.comap
    ((LinearMap.id : IntervalSobolevL2 l r →ₗ[ℝ] IntervalSobolevL2 l r).prod
      (P.principalValue • LinearMap.id))

theorem SignedIntervalPointProblem.mem_principalEigenspace
    (P : SignedIntervalPointProblem ι l r) (u : IntervalSobolevL2 l r) :
    u ∈ P.principalEigenspace ↔ (u, P.principalValue • u) ∈ P.operator.graph := Iff.rfl

theorem SignedIntervalPointProblem.principalEigenspace_finrank
    (P : SignedIntervalPointProblem ι l r) : Module.finrank ℝ P.principalEigenspace = 1 := by
  obtain ⟨u, hu, _hpos, hm, _hweak, hg⟩ := P.positive_principal_eigenstate
  let f := (ofEnergy hu P.interval_pos).state
  have hf : f ≠ 0 := by
    intro hzero
    have he : ‖f‖ ^ 2 = P.squareMass u := P.squareMass_ofEnergy hu
    rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at he
    exact hm.ne' he.symm
  let e : P.principalEigenspace := ⟨f, (P.mem_principalEigenspace f).mpr hg⟩
  apply finrank_eq_one e
  · intro he
    exact hf (congrArg Subtype.val he)
  · intro w
    obtain ⟨c, hc⟩ := P.principal_operator_scalar hf hg
      ((P.mem_principalEigenspace w.val).mp w.property)
    refine ⟨c, Subtype.ext ?_⟩
    exact hc.symm

end TimeTraps.Analysis
