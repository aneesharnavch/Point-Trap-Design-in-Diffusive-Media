module

public import TimeTraps.Analysis.GraphContactOperatorOrderLoad

@[expose] public section

/-! Coercivity forces the actual network solution of a nonnegative edge
L2 source to equal its absolute representative. Thus every closed edge
and every recovered node has nonnegative state, as does the L2 inverse.
The original connected, finite, nonempty-edge network with nonnegative
vertex strengths and one positive reaction is retained throughout. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphContactOperatorProblem.operatorSolution_eq_orderAbs (P : GraphContactOperatorProblem V E)
    (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    P.operatorSolution f = P.operatorOrderAbs (P.operatorSolution f) := by
  let u := P.operatorSolution f
  let v := P.operatorOrderAbs u
  have he : P.operatorForm (u - v) (u - v) = 2 * P.operatorForm u (u - v) := by
    simp only [map_sub, sub_apply]
    have hv : P.operatorForm v v = P.operatorForm u u := P.operatorForm_orderAbs u
    rw [P.operatorForm_symmetric v u, hv]
    ring
  have hn : P.operatorForm (u - v) (u - v) ≤ 0 := by
    rw [he]
    have hs : P.operatorForm u (u - v) =
        inner ℝ f (graphSobolevSpaceStateL P.geometry (u - v)) :=
      P.operatorSolution_spec f (u - v)
    rw [hs]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (P.operatorOrderAbs_load_nonpos f hf u)
  obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
  have hz := (hb (u - v)).trans hn
  change u = v
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  by_contra hn
  have hp : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  exact (not_le_of_gt (mul_pos (mul_pos hc hp) hp)) hz

theorem GraphContactOperatorProblem.operatorSolution_representative_nonneg (P : GraphContactOperatorProblem V E)
    (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    ∀ e, ∀ x ∈ Icc 0 (P.geometry.length e), 0 ≤ P.operatorRep (P.operatorSolution f) e x := by
  intro e x hx
  have he := P.operatorOrderAbs_representative (P.operatorSolution f) e hx
  rw [← P.operatorSolution_eq_orderAbs f hf] at he
  exact he.symm ▸ abs_nonneg (P.operatorRep (P.operatorSolution f) e x)

theorem GraphContactOperatorProblem.operatorSolution_nodes_nonneg (P : GraphContactOperatorProblem V E)
    (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    ∀ v, 0 ≤ P.operatorNodes (P.operatorSolution f) v := by
  intro v
  have he := P.operatorOrderAbs_nodes (P.operatorSolution f) v
  rw [← P.operatorSolution_eq_orderAbs f hf] at he
  exact he.symm ▸ abs_nonneg (P.operatorNodes (P.operatorSolution f) v)

theorem GraphContactOperatorProblem.operatorInverse_nonneg_ae (P : GraphContactOperatorProblem V E)
    (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (P.operatorInverse f e) x := by
  intro e
  rw [P.operatorInverse_apply]
  have hrep : (graphSobolevSpaceStateL P.geometry (P.operatorSolution f)) e
      =ᵐ[volume.restrict (Ioo 0 (P.geometry.length e))] P.operatorRep (P.operatorSolution f) e :=
    graphSobolevRepresentative_state_ae P.geometry (P.operatorSolution f).val e
  filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with x hx hi
  rw [hx]
  exact P.operatorSolution_representative_nonneg f hf e x (Ioo_subset_Icc_self hi)

theorem GraphContactL2WeakEquation.nonneg_of_source_nonneg {P : GraphContactOperatorProblem V E}
    {f : GraphL2Product P.geometry} {U : V → ℝ} {u : E → ℝ → ℝ}
    (h : GraphContactL2WeakEquation P f U u)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    (∀ v, 0 ≤ U v) ∧ ∀ e, ∀ x ∈ Icc 0 (P.geometry.length e), 0 ≤ u e x := by
  have hn := P.operatorNodes_ofEnergy h.energy
  rw [h.to_operatorSolution] at hn
  constructor
  · rw [← hn]
    exact P.operatorSolution_nodes_nonneg f hf
  · intro e x hx
    have he := P.operatorRep_ofEnergy h.energy e hx
    rw [h.to_operatorSolution] at he
    rw [← he]
    exact P.operatorSolution_representative_nonneg f hf e x hx

end TimeTraps.Analysis
