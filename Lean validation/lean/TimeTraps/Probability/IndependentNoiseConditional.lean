module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

@[expose] public section

/-! A past-measurable parameter and noise independent of the entire past
have a product law after restriction to any past event. This proves the
conditional expectation formula for every bounded Borel function of the
parameter and noise, by the defining integral identities on past events. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem independentNoise_map_pair_restrict [IsFiniteMeasure P]
    (hm : m ≤ mΩ) {Y Z : Ω → ℝ}
    (hY : Measurable[m] Y) (hZ : Measurable Z)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) m P)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    (P.restrict A).map (fun ω => (Y ω, Z ω)) =
      ((P.restrict A).map Y).prod (P.map Z) := by
  have hY₀ : Measurable Y := hY.mono hm le_rfl
  apply (Measure.prod_eq ?_).symm
  intro s t hs ht
  rw [Measure.map_apply (hY₀.prodMk hZ) (hs.prod ht),
    Measure.restrict_apply ((hY₀.prodMk hZ) (hs.prod ht)),
    Measure.map_apply hY₀ hs, Measure.restrict_apply (hY₀ hs), Measure.map_apply hZ ht]
  change P (((Y ⁻¹' s) ∩ (Z ⁻¹' t)) ∩ A) = P (Y ⁻¹' s ∩ A) * P (Z ⁻¹' t)
  calc
    _ = P (Z ⁻¹' t ∩ (Y ⁻¹' s ∩ A)) := congrArg P (by ext ω; simp only [mem_inter_iff]; tauto)
    _ = P (Z ⁻¹' t) * P (Y ⁻¹' s ∩ A) :=
      (Indep_iff _ _ _).mp hind _ _ ⟨t, ht, rfl⟩ ((hY hs).inter hA)
    _ = _ := mul_comm _ _

theorem independentNoise_condExp_bounded [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {Y Z : Ω → ℝ}
    (hY : Measurable[m] Y) (hZ : Measurable Z)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) m P)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ p, |f p| ≤ M) :
    P[fun ω => f (Y ω, Z ω) | m] =ᵐ[P]
      fun ω => ∫ z, f (Y ω, z) ∂P.map Z := by
  have hY₀ : Measurable Y := hY.mono hm le_rfl
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  let Φ : ℝ → ℝ := fun y => ∫ z, f (y, z) ∂P.map Z
  have hΦ : StronglyMeasurable Φ := hf.stronglyMeasurable.integral_prod_right'
  have hΦb (y : ℝ) : ‖Φ y‖ ≤ M := by
    have h := norm_integral_le_of_norm_le_const
      (μ := P.map Z) (f := fun z => f (y, z))
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb (y, z))
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h
  have hfi : Integrable (fun ω => f (Y ω, Z ω)) P :=
    (integrable_const M).mono' (hf.comp (hY₀.prodMk hZ)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb (Y ω, Z ω))
  have hΦi : Integrable (fun ω => Φ (Y ω)) P :=
    (integrable_const M).mono' (hΦ.comp_measurable hY₀).aestronglyMeasurable
      (Eventually.of_forall fun ω => hΦb (Y ω))
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hfi
    (fun _ _ _ => hΦi.integrableOn) ?_ (hΦ.comp_measurable hY).aestronglyMeasurable).symm
  intro A hA _
  have hprod : Integrable f (((P.restrict A).map Y).prod (P.map Z)) :=
    (integrable_const M).mono' hf.aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hb p)
  calc
    (∫ ω in A, Φ (Y ω) ∂P) = ∫ y, Φ y ∂(P.restrict A).map Y :=
      (integral_map hY₀.aemeasurable hΦ.aestronglyMeasurable).symm
    _ = ∫ p, f p ∂((P.restrict A).map Y).prod (P.map Z) := (integral_prod f hprod).symm
    _ = ∫ p, f p ∂(P.restrict A).map (fun ω => (Y ω, Z ω)) := by
      rw [independentNoise_map_pair_restrict hm hY hZ hind hA]
    _ = ∫ ω in A, f (Y ω, Z ω) ∂P :=
      integral_map (hY₀.prodMk hZ).aemeasurable hf.aestronglyMeasurable

end TimeTraps.Probability
