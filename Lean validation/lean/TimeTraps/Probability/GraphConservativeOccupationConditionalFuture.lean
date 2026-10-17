module

public import TimeTraps.Probability.GraphConservativeOccupationConditionalData

@[expose] public section

/-! Conditional occupation of a future deterministic time interval.
Conditional Fubini uses a genuinely jointly measurable version in the
conditioning sigma algebra and the literal elapsed-time potential. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupation_future_condExp_of_transition
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ))
    (m : MeasurableSpace (GraphContinuousPath P.geometry)) (hm : m ≤ graphContinuousPathMeasurableSpace P.geometry)
    {s H : ℝ≥0} (hsH : s ≤ H)
    (hs : StronglyMeasurable[m] (fun p : GraphContinuousPath P.geometry => p s))
    (hcond : ∀ r : ℝ≥0, s ≤ r →
      (P.continuousPathLaw hκ x)[fun p => f (p r) | m] =ᵐ[P.continuousPathLaw hκ x]
        (fun p => P.realizedFeller (r - s) f (p s))) :
    (P.continuousPathLaw hκ x)[fun p : GraphContinuousPath P.geometry =>
      ∫ r in s.val..H.val, f (p r.toNNReal) | m] =ᵐ[P.continuousPathLaw hκ x]
        (fun p => P.occupationPotential f (H.val - s.val) (p s)) := by
  let mΩ : MeasurableSpace (GraphContinuousPath P.geometry) := graphContinuousPathMeasurableSpace P.geometry
  let inst := P.continuousPathLaw_probability hκ x
  let ν : Measure ℝ := volume.restrict (Ioc s.val H.val)
  let F : ℝ × GraphContinuousPath P.geometry → ℝ := fun q => f (q.2 q.1.toNNReal)
  let G : ℝ × GraphContinuousPath P.geometry → ℝ :=
    fun q => P.realizedFeller (q.1.toNNReal - s) f (q.2 s)
  have hFm : Measurable F := by dsimp [F]; fun_prop
  have hF : Integrable F (ν.prod (P.continuousPathLaw hκ x)) :=
    (integrable_const ‖f‖).mono' hFm.aestronglyMeasurable
      (Eventually.of_forall (fun q => f.norm_coe_le_norm _))
  have hGm : @StronglyMeasurable (ℝ × GraphContinuousPath P.geometry) ℝ _
      (MeasurableSpace.prod inferInstance m) G := by
    let : MeasurableSpace (GraphContinuousPath P.geometry) := m
    exact ((P.occupation_future_section_continuous f s).measurable.comp
      (measurable_fst.prodMk (hs.measurable.comp measurable_snd))).stronglyMeasurable
  have hprod : MeasurableSpace.prod (inferInstance : MeasurableSpace ℝ) m ≤
      MeasurableSpace.prod inferInstance (inferInstance : MeasurableSpace (GraphContinuousPath P.geometry)) :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono hm)
  have hGambient : Measurable G := hGm.measurable.mono hprod le_rfl
  have hG : Integrable G (ν.prod (P.continuousPathLaw hκ x)) := by
    apply (integrable_const ‖f‖).mono' hGambient.aestronglyMeasurable
    exact Eventually.of_forall (fun q =>
      ((P.realizedFeller (q.1.toNNReal - s) f).norm_coe_le_norm _).trans
        (P.realizedFeller_norm_le _ f))
  have hsection : ∀ᵐ r ∂ν,
      (P.continuousPathLaw hκ x)[fun p => F (r, p) | m] =ᵐ[P.continuousPathLaw hκ x]
        (fun p => G (r, p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have he : r.toNNReal.val = r := Real.coe_toNNReal r (s.coe_nonneg.trans hr.1.le)
    have hsr : s ≤ r.toNNReal := show s.val ≤ r.toNNReal.val from hr.1.le.trans_eq he.symm
    exact hcond _ hsr
  have hc := condExp_integral_sections (ν := ν) (P := P.continuousPathLaw hκ x) hm hF hG hGm hsection
  have hFi (p : GraphContinuousPath P.geometry) :
      (∫ r, F (r, p) ∂ν) = ∫ r in s.val..H.val, f (p r.toNNReal) :=
    (intervalIntegral.integral_of_le (show s.val ≤ H.val from hsH)).symm
  have hGi (p : GraphContinuousPath P.geometry) :
      (∫ r, G (r, p) ∂ν) = P.occupationPotential f (H.val - s.val) (p s) :=
    (intervalIntegral.integral_of_le (show s.val ≤ H.val from hsH)).symm.trans
      (P.occupation_future_section_integral f hsH (p s))
  simpa only [hFi, hGi] using hc

end TimeTraps.Analysis
