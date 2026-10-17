module

public import TimeTraps.Analysis.IntervalSobolevRepresentation
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

/-! A bundled Hilbert Sobolev space. The weak-derivative graph is a closed
linear subspace of the L2 product with its sum-of-squares norm, cut out by
every smooth compact interior test. No absolute continuity is assumed in
this construction. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology ContDiff Distributions InnerProductSpace

noncomputable section

abbrev IntervalSobolevL2 (l r : ℝ) := Lp ℝ 2 (volume.restrict (Ioo l r))

abbrev IntervalSobolevPair (l r : ℝ) :=
  WithLp 2 (IntervalSobolevL2 l r × IntervalSobolevL2 l r)

abbrev IntervalSobolevTest (l r : ℝ) := 𝓓(⟨Ioo l r, isOpen_Ioo⟩, ℝ)

noncomputable def intervalSobolevTestVector {l r : ℝ} (φ : IntervalSobolevTest l r) :
    IntervalSobolevPair l r :=
  WithLp.toLp 2
    (((φ.contDiff.continuous_deriv (by simp)).memLp_of_hasCompactSupport
      φ.hasCompactSupport.deriv).toLp (deriv φ),
      (φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ)

noncomputable def intervalSobolevTestForm {l r : ℝ} (φ : IntervalSobolevTest l r) :
    IntervalSobolevPair l r →L[ℝ] ℝ := innerSL ℝ (intervalSobolevTestVector φ)

theorem intervalSobolevL2_test_pairing {l r : ℝ} (f : IntervalSobolevL2 l r)
    {φ : ℝ → ℝ} (hφ : MemLp φ 2 (volume.restrict (Ioo l r)))
    (hs : tsupport φ ⊆ Ioo l r) :
    ⟪hφ.toLp φ, f⟫_ℝ = ∫ x, f x * φ x := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in Ioo l r, f x * φ x := by
      apply integral_congr_ae
      filter_upwards [hφ.coeFn_toLp] with x hx
      simp only [Real.inner_apply, hx, mul_comm]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : φ x = 0 := by
        by_contra hn
        exact hx (hs (subset_closure hn))
      rw [hz, mul_zero]

theorem intervalSobolevTestForm_apply {l r : ℝ} (φ : IntervalSobolevTest l r)
    (u : IntervalSobolevPair l r) :
    intervalSobolevTestForm φ u =
      (∫ x, u.fst x * deriv φ x) + ∫ x, u.snd x * φ x := by
  change ⟪_, u.fst⟫_ℝ + ⟪_, u.snd⟫_ℝ = _
  dsimp only [intervalSobolevTestVector, WithLp.toLp_fst, WithLp.toLp_snd]
  rw [intervalSobolevL2_test_pairing _ _ (tsupport_deriv_subset.trans φ.tsupport_subset),
    intervalSobolevL2_test_pairing _ _ φ.tsupport_subset]

noncomputable def intervalSobolevGraph (l r : ℝ) : Submodule ℝ (IntervalSobolevPair l r) :=
  ⨅ φ : IntervalSobolevTest l r, (intervalSobolevTestForm φ).ker

theorem intervalSobolevGraph_mem_iff {l r : ℝ} (u : IntervalSobolevPair l r) :
    u ∈ intervalSobolevGraph l r ↔ IntervalWeakDerivative u.fst u.snd l r := by
  rw [intervalWeakDerivative_iff_testFunction]
  change (u ∈ ⨅ φ : IntervalSobolevTest l r, (intervalSobolevTestForm φ).ker) ↔ _
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    intervalSobolevTestForm_apply, add_eq_zero_iff_eq_neg]

theorem intervalSobolevGraph_isClosed (l r : ℝ) :
    IsClosed (intervalSobolevGraph l r : Set (IntervalSobolevPair l r)) := by
  unfold intervalSobolevGraph
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun φ => (intervalSobolevTestForm φ).isClosed_ker

abbrev IntervalSobolevSpace (l r : ℝ) := ↥(intervalSobolevGraph l r)

instance intervalSobolevSpace_complete (l r : ℝ) : CompleteSpace (IntervalSobolevSpace l r) :=
  (intervalSobolevGraph_isClosed l r).completeSpace_coe

noncomputable def IntervalSobolevSpace.state {l r : ℝ} (u : IntervalSobolevSpace l r) :
    IntervalSobolevL2 l r := u.val.fst

noncomputable def IntervalSobolevSpace.gradient {l r : ℝ} (u : IntervalSobolevSpace l r) :
    IntervalSobolevL2 l r := u.val.snd

theorem IntervalSobolevSpace.weakDerivative {l r : ℝ} (u : IntervalSobolevSpace l r) :
    IntervalWeakDerivative u.state u.gradient l r :=
  (intervalSobolevGraph_mem_iff u.val).mp u.property

theorem IntervalSobolevSpace.norm_sq {l r : ℝ} (u : IntervalSobolevSpace l r) :
    ‖u‖ ^ 2 = (∫ x in Ioo l r, u.state x ^ 2) + ∫ x in Ioo l r, u.gradient x ^ 2 := by
  change ‖u.val‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
  simp only [Real.inner_apply, pow_two, IntervalSobolevSpace.state,
    IntervalSobolevSpace.gradient]

end

end TimeTraps.Analysis
