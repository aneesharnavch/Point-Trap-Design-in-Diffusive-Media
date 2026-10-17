module

public import TimeTraps.Analysis.RegularSturmPositiveGroundAttainment
public import TimeTraps.Analysis.RegularSturmPositiveGroundSimplicity
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

/-! The actual regular variable-coefficient Sturm operator has a one-dimensional
principal eigenspace. The eigenspace is defined from its original L2
operator graph, and simplicity follows from the full H1 weak equation. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.principal_operator_scalar
    (P : RegularSturmProblem ι l r) {u v : IntervalSobolevL2 l r}
    (hu₀ : u ≠ 0) (hu : (u, P.principalValue • u) ∈ P.operator.graph)
    (hv : (v, P.principalValue • v) ∈ P.operator.graph) :
    ∃ c : ℝ, v = c • u := by
  obtain ⟨U, hU, heU⟩ := (P.operator_graph_iff_hilbert _ _).mp hu
  obtain ⟨V, hV, heV⟩ := (P.operator_graph_iff_hilbert _ _).mp hv
  have hEU : ∀ w : IntervalSeparatedSpace P.boundary,
      P.form U w = P.principalValue * inner ℝ (P.stateL U) (P.stateL w) := by
    intro w
    rw [heU w, real_inner_smul_left, hU]
  have hEV : ∀ w : IntervalSeparatedSpace P.boundary,
      P.form V w = P.principalValue * inner ℝ (P.stateL V) (P.stateL w) := by
    intro w
    rw [heV w, real_inner_smul_left, hV]
  let x := (l + r) / 2
  have hx : x ∈ Ioo l r := by
    have h := P.boundary.interval_pos
    constructor <;> dsimp only [x] <;> linarith
  have hU₀ : U.val.representative P.boundary.interval_pos x ≠ 0 := by
    intro hz
    have hzero := P.principal_hilbert_zero_of_interior_zero U hEU hx hz
    apply hu₀
    rw [← hU, hzero, map_zero]
  let c := V.val.representative P.boundary.interval_pos x /
    U.val.representative P.boundary.interval_pos x
  have he : V = c • U := P.principal_hilbert_scalar U V hx hU₀ hEU hEV
  refine ⟨c, ?_⟩
  calc
    v = P.stateL V := hV.symm
    _ = c • P.stateL U := by rw [he, map_smul]
    _ = c • u := by rw [hU]

noncomputable def RegularSturmProblem.principalEigenspace
    (P : RegularSturmProblem ι l r) : Submodule ℝ (IntervalSobolevL2 l r) :=
  P.operator.graph.comap
    ((LinearMap.id : IntervalSobolevL2 l r →ₗ[ℝ] IntervalSobolevL2 l r).prod
      (P.principalValue • LinearMap.id))

theorem RegularSturmProblem.mem_principalEigenspace
    (P : RegularSturmProblem ι l r) (u : IntervalSobolevL2 l r) :
    u ∈ P.principalEigenspace ↔ (u, P.principalValue • u) ∈ P.operator.graph := Iff.rfl

theorem RegularSturmProblem.principalEigenspace_finrank
    (P : RegularSturmProblem ι l r) : Module.finrank ℝ P.principalEigenspace = 1 := by
  obtain ⟨u, hu, huz, _hp, hm, _he, hg⟩ := P.positive_principal_eigenstate
  let f := P.stateL (P.boundary.ofEnergy hu huz)
  have hf : f ≠ 0 := by
    intro hz
    have hnorm : ‖f‖ ^ 2 = P.squareMass u := P.squareMass_ofEnergy hu huz
    rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
    exact hm.ne' hnorm.symm
  let e : P.principalEigenspace := ⟨f, (P.mem_principalEigenspace f).mpr hg⟩
  apply finrank_eq_one e
  · intro he
    exact hf (congrArg Subtype.val he)
  · intro w
    obtain ⟨c, hc⟩ := P.principal_operator_scalar hf hg
      ((P.mem_principalEigenspace w.val).mp w.property)
    exact ⟨c, Subtype.ext hc.symm⟩

end TimeTraps.Analysis
