module

public import TimeTraps.Probability.BrownianIntegralPastMultiplierDomain

@[expose] public section

/-! Canonical pull-out for a bounded raw-F_s variable and every actual
future-supported integrand. Both sides are continuous maps on the closed
future subspace, and equality is derived on elementary generators before
passing to its closure. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
variable {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}
variable {Z : Ω → ℝ} {M : ℝ≥0} {s : ℝ≥0}

theorem brownianClosedSpanContinuousLinearMap_ext {I E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : I → E)
    (L R : (Submodule.span ℝ (range g)).topologicalClosure →L[ℝ] F)
    (hgen : ∀ i, L (TimeTraps.Analysis.gramClosureGenerator g i) =
      R (TimeTraps.Analysis.gramClosureGenerator g i)) : L = R := by
  let inclusion := TimeTraps.Analysis.gramClosureInclusion g
  let LS := L.comp inclusion.toContinuousLinearMap
  let RS := R.comp inclusion.toContinuousLinearMap
  have hspan : ∀ v (hv : v ∈ Submodule.span ℝ (range g)), LS ⟨v, hv⟩ = RS ⟨v, hv⟩ := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      exact hgen a
    | zero => exact (map_zero LS).trans (map_zero RS).symm
    | add v w hv hw ihv ihw =>
      change LS (⟨v, hv⟩ + ⟨w, hw⟩) = RS (⟨v, hv⟩ + ⟨w, hw⟩)
      rw [LS.map_add, RS.map_add, ihv, ihw]
    | smul c v hv ih =>
      change LS (c • ⟨v, hv⟩) = RS (c • ⟨v, hv⟩)
      rw [LS.map_smul, RS.map_smul, ih]
  apply ContinuousLinearMap.ext
  intro f
  refine (TimeTraps.Analysis.gramClosureInclusion_dense g).induction_on f
    (isClosed_eq L.continuous R.continuous) ?_
  intro v
  exact hspan v.val v.property

theorem brownianPastMultiplier_integral (hB : IsPreBrownianReal B P)
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) (f : brownianIntegralFutureSpace B hBm P s) :
    brownianIntegral hB (brownianPastMultiplier hZ hb f) =
      brownianPastMultiplierL2 (hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable hb
        (brownianIntegral hB f.val) := by
  let g := fun a : {a : BrownianIntegralElementary B hBm P // s ≤ a.left} =>
    brownianIntegralGenerator a.val
  let L : brownianIntegralFutureSpace B hBm P s →L[ℝ] Lp ℝ 2 P :=
    (brownianIntegral hB).toContinuousLinearMap.comp (brownianPastMultiplier hZ hb)
  let R : brownianIntegralFutureSpace B hBm P s →L[ℝ] Lp ℝ 2 P :=
    (brownianPastMultiplierL2
      (hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable hb).comp
        ((brownianIntegral hB).toContinuousLinearMap.comp
          (brownianIntegralFutureSpace B hBm P s).subtypeL)
  have hgen (a : {a : BrownianIntegralElementary B hBm P // s ≤ a.left}) :
      L (TimeTraps.Analysis.gramClosureGenerator g a) =
        R (TimeTraps.Analysis.gramClosureGenerator g a) := by
    change brownianIntegral hB (brownianPastMultiplier hZ hb
      ⟨brownianIntegralGenerator a.val, brownianIntegralGenerator_mem_future a.val a.property⟩) =
      brownianPastMultiplierL2 (hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable hb
        (brownianIntegral hB (brownianIntegralGenerator a.val))
    rw [brownianPastMultiplier_generator, brownianIntegral_generator, brownianIntegral_generator]
    exact brownianPastMultiplier_elementary_integral hB a.val a.property hZ hb
  change L f = R f
  exact congrArg (fun A => A f) (brownianClosedSpanContinuousLinearMap_ext g L R hgen)

theorem brownianPastMultiplier_integral_ae (hB : IsPreBrownianReal B P)
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) (f : brownianIntegralFutureSpace B hBm P s) :
    brownianIntegral hB (brownianPastMultiplier hZ hb f) =ᵐ[P]
      (fun ω => Z ω * brownianIntegral hB f.val ω) := by
  rw [brownianPastMultiplier_integral]
  exact brownianPastMultiplierL2_coe _ _ _

theorem brownianIntegral_mem_future_of_cutoff_zero
    (f : brownianIntegralSpace B hBm P) (hf : brownianTimeCutoff B hBm P s f = 0) :
    f ∈ brownianIntegralFutureSpace B hBm P s := by
  have h := brownianTimeCutoff_sub_mem_future s f
  rwa [hf, sub_zero] at h

theorem brownianIntegral_mem_future_of_support
    (f : brownianIntegralSpace B hBm P)
    (hf : ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      p.1 ≤ s.val → (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p = 0) :
    f ∈ brownianIntegralFutureSpace B hBm P s := by
  apply brownianIntegral_mem_future_of_cutoff_zero f
  apply Subtype.ext
  change (brownianTimeCutoff B hBm P s f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) = 0
  apply Lp.ext
  filter_upwards [brownianTimeCutoff_coe s f, hf,
    Lp.coeFn_zero ℝ 2 ((volume : Measure ℝ).prod P)] with p hc hf hz
  rw [hc, hz]
  by_cases hp : p ∈ brownianTimePast s
  · rw [Set.indicator_of_mem hp]
    exact hf hp
  · rw [Set.indicator_of_notMem hp]
    rfl

end TimeTraps.Probability

end
