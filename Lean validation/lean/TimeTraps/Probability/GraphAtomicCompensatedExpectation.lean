module

public import TimeTraps.Probability.GraphAtomicCompensatedLimit

@[expose] public section

/-! Finite-horizon expectations from the original graph Dynkin
martingale. All weighted terms are genuinely integrable; the contact
identity leaves exactly the original rho-weighted running cost. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

theorem GraphShiftedContactOperatorProblem.atomicFiniteResidual_of_martingale
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (u : C(GraphRealization P.geometry, ℝ))
    (hM : Martingale (P.atomicCompensatedProcess b hb a κ u)
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw h0 x)) (T : ℝ≥0) :
    Integrable (P.atomicFiniteResidual b a κ u T) (P.continuousPathLaw h0 x) ∧
      (∫ p, P.atomicFiniteResidual b a κ u T p ∂P.continuousPathLaw h0 x) = 0 := by
  let _ := P.continuousPathLaw_probability h0 x
  have hH := P.atomicSurvival_stronglyAdapted a κ
  have hbound (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ‖P.atomicSurvival a κ t p‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (P.atomicSurvival_bounds a κ hκ t p).1]
    exact (P.atomicSurvival_bounds a κ hκ t p).2
  have hMc := P.atomicCompensatedProcess_continuous_ae h0 x b hb a κ u
  have hHK := P.atomicSurvival_eq_one_sub_loss_ae h0 x a κ hκ
  have hK : ∀ᵐ p ∂P.continuousPathLaw h0 x, ∀ t ∈ Icc 0 T,
      0 ≤ P.atomicSurvivalLossStieltjes a κ hκ p (t : ℝ) ∧
        P.atomicSurvivalLossStieltjes a κ hκ p (t : ℝ) ≤ 1 :=
    Eventually.of_forall (fun p t _ => P.atomicSurvivalLossStieltjes_bounds a κ hκ p (t : ℝ))
  have hprod := martingaleStieltjesProduct_integrable_mean hM hH hbound
    (P.atomicSurvivalLossStieltjes a κ hκ) T (P.atomicCompensatedBound b hb a κ u T)
    (P.atomicCompensatedBound_integrable h0 x b hb a κ u T) hMc hHK hK
    (P.atomicCompensatedProcess_bound_ae h0 x b hb a κ u T)
  have he : P.atomicFiniteResidual b a κ u T =ᵐ[P.continuousPathLaw h0 x]
      martingaleStieltjesProduct (P.atomicCompensatedProcess b hb a κ u)
        (P.atomicSurvival a κ) (P.atomicSurvivalLossStieltjes a κ hκ) T := by
    filter_upwards [P.atomicCompensatedProcess_weighted_limit h0 x b hb a κ hκ u T,
      martingaleDyadicWeightedSum_stieltjes_tendsto (P.atomicSurvivalLossStieltjes a κ hκ) T hMc hHK]
      with p hp hq
    exact tendsto_nhds_unique hp hq
  exact ⟨hprod.1.congr he.symm, (integral_congr_ae he).trans hprod.2⟩

theorem GraphShiftedContactOperatorProblem.atomicRunningCost_finite_of_martingale
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (u : C(GraphRealization P.geometry, ℝ))
    (hM : Martingale (P.atomicCompensatedProcess b hb a κ u)
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw h0 x)) (T : ℝ≥0) :
    Integrable (fun p => ∫ r in Ioc (0 : ℝ) (T : ℝ),
      P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal)) (P.continuousPathLaw h0 x) ∧
    (∫ p, (∫ r in Ioc (0 : ℝ) (T : ℝ),
      P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal)) ∂P.continuousPathLaw h0 x) =
      u x - ∫ p, P.atomicSurvival a κ T p * u (p T) ∂P.continuousPathLaw h0 x := by
  let _ := P.continuousPathLaw_probability h0 x
  let F := fun p => P.atomicSurvival a κ T p * u (p T)
  let G := fun p : GraphContinuousPath P.geometry => u (p 0)
  let C := fun p => ∫ r in Ioc (0 : ℝ) (T : ℝ),
    P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal)
  have hG : Integrable G (P.continuousPathLaw h0 x) := by
    apply (integrable_const ‖u‖).mono'
      (u.continuous.comp (continuous_eval_const 0)).measurable.aestronglyMeasurable
    exact Eventually.of_forall (fun p => u.norm_coe_le_norm (p 0))
  have hH := ((P.atomicSurvival_stronglyAdapted a κ) T).mono ((graphContinuousNaturalFiltration P.geometry).le T)
  have hF : Integrable F (P.continuousPathLaw h0 x) := by
    have hu : Integrable (fun p : GraphContinuousPath P.geometry => u (p T)) (P.continuousPathLaw h0 x) := by
      apply (integrable_const ‖u‖).mono'
        (u.continuous.comp (continuous_eval_const T)).measurable.aestronglyMeasurable
      exact Eventually.of_forall (fun p => u.norm_coe_le_norm (p T))
    apply hu.bdd_mul hH.aestronglyMeasurable
    apply Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs, abs_of_pos (P.atomicSurvival_bounds a κ hκ T p).1]
    exact (P.atomicSurvival_bounds a κ hκ T p).2
  have hr := P.atomicFiniteResidual_of_martingale h0 x b hb a κ hκ u hM T
  have he : C = fun p => P.atomicFiniteResidual b a κ u T p - (F p - G p) := by
    funext p
    change C p = F p - G p + C p - (F p - G p)
    ring
  have hC : Integrable C (P.continuousPathLaw h0 x) := by
    rw [he]
    exact hr.1.sub (hF.sub hG)
  refine ⟨hC, ?_⟩
  have hstart : (∫ p, G p ∂P.continuousPathLaw h0 x) = u x := by
    have heq : G =ᵐ[P.continuousPathLaw h0 x] (fun _ => u x) :=
      (P.continuousPathLaw_initial h0 x).mono (fun p hp => congrArg u hp)
    rw [integral_congr_ae heq]
    simp only [integral_const, probReal_univ, one_smul]
  have hi : (∫ p, P.atomicFiniteResidual b a κ u T p ∂P.continuousPathLaw h0 x) =
      (∫ p, F p ∂P.continuousPathLaw h0 x) - (∫ p, G p ∂P.continuousPathLaw h0 x) +
        ∫ p, C p ∂P.continuousPathLaw h0 x := by
    change (∫ p, F p - G p + C p ∂P.continuousPathLaw h0 x) = _
    have hFG : Integrable (fun p => F p - G p) (P.continuousPathLaw h0 x) := hF.sub hG
    rw [integral_add hFG hC, integral_sub hF hG]
  rw [hr.2, hstart] at hi
  change (∫ p, C p ∂P.continuousPathLaw h0 x) = u x - ∫ p, F p ∂P.continuousPathLaw h0 x
  linarith

end TimeTraps.Analysis
