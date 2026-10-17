module

public import TimeTraps.Probability.BrownianIntegralMartingale

@[expose] public section

/-! Martingale increments are the integrals of the actual product-L²
integrand restricted to a deterministic time interval. Their second
moment is the L² mass of that restriction. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

def brownianTimeWindow (s t : ℝ≥0) : Set (ℝ × Ω) :=
  {p | s.val < p.1 ∧ p.1 ≤ t.val}

theorem brownianTimeWindow_measurable (s t : ℝ≥0) :
    MeasurableSet (brownianTimeWindow (Ω := Ω) s t) :=
  (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)

theorem brownianTimeCutoff_sub_coe {s t : ℝ≥0} (hst : s ≤ t)
    (f : brownianIntegralSpace B hBm P) :
    ((brownianTimeCutoff B hBm P t f - brownianTimeCutoff B hBm P s f) :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (brownianTimeWindow s t).indicator (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) := by
  filter_upwards [Lp.coeFn_sub
      (brownianTimeCutoff B hBm P t f : Lp ℝ 2 ((volume : Measure ℝ).prod P))
      (brownianTimeCutoff B hBm P s f : Lp ℝ 2 ((volume : Measure ℝ).prod P)),
    brownianTimeCutoff_coe t f, brownianTimeCutoff_coe s f] with p hsub ht hs
  rw [hsub, Pi.sub_apply, ht, hs]
  have hst' : s.val ≤ t.val := hst
  by_cases hps : p ∈ brownianTimePast s
  · have hpt : p ∈ brownianTimePast t := (show p.1 ≤ s.val from hps).trans hst'
    have hpw : p ∉ brownianTimeWindow s t := fun h => (not_lt_of_ge hps) h.1
    rw [indicator_of_mem hpt, indicator_of_mem hps, indicator_of_notMem hpw, sub_self]
  · have hsp : s.val < p.1 := lt_of_not_ge hps
    by_cases hpt : p ∈ brownianTimePast t
    · have hpw : p ∈ brownianTimeWindow s t := ⟨hsp, hpt⟩
      rw [indicator_of_mem hpt, indicator_of_notMem hps, indicator_of_mem hpw, sub_zero]
    · have hpw : p ∉ brownianTimeWindow s t := fun h => hpt h.2
      rw [indicator_of_notMem hpt, indicator_of_notMem hps, indicator_of_notMem hpw, sub_zero]

theorem brownianIntegralProcess_increment_ae (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (s t : ℝ≥0) :
    (fun ω => brownianIntegralProcess hB f t ω - brownianIntegralProcess hB f s ω) =ᵐ[P]
      brownianIntegral hB
        (brownianTimeCutoff B hBm P t f - brownianTimeCutoff B hBm P s f) := by
  have hI : brownianIntegral hB
      (brownianTimeCutoff B hBm P t f - brownianTimeCutoff B hBm P s f) =ᵐ[P]
      (fun ω => brownianIntegralUpTo hB t f ω - brownianIntegralUpTo hB s f ω) := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  exact ((brownianIntegralProcess_ae hB f t).sub
    (brownianIntegralProcess_ae hB f s)).trans hI.symm

theorem brownianIntegralProcess_increment_isometry (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (brownianIntegralProcess hB f t ω - brownianIntegralProcess hB f s ω) ^ 2 ∂P) =
      ∫ p in brownianTimeWindow s t,
        (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ^ 2 ∂volume.prod P := by
  calc
    _ = ∫ ω, (brownianIntegral hB
        (brownianTimeCutoff B hBm P t f - brownianTimeCutoff B hBm P s f)) ω ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [brownianIntegralProcess_increment_ae hB f s t] with ω hω
      rw [hω]
    _ = ∫ p, ((brownianTimeCutoff B hBm P t f - brownianTimeCutoff B hBm P s f) :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ^ 2 ∂volume.prod P :=
      brownianIntegral_isometry hB _
    _ = ∫ p, (brownianTimeWindow s t).indicator
        (fun p => (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ^ 2) p ∂volume.prod P := by
      apply integral_congr_ae
      filter_upwards [brownianTimeCutoff_sub_coe hst f] with p hp
      rw [hp]
      by_cases hmem : p ∈ brownianTimeWindow s t <;> simp [hmem]
    _ = _ := integral_indicator (brownianTimeWindow_measurable s t)

theorem brownianIntegralProcess_increment_condExp_zero (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => brownianIntegralProcess hB f t ω - brownianIntegralProcess hB f s ω |
      brownianNaturalFiltration B hBm s] =ᵐ[P] 0 := by
  have hM := brownianIntegralProcess_martingale hB f
  refine (condExp_sub (hM.integrable t) (hM.integrable s)
    (brownianNaturalFiltration B hBm s)).trans ?_
  filter_upwards [hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s)] with ω ht hs
  change P[brownianIntegralProcess hB f t | brownianNaturalFiltration B hBm s] ω -
    P[brownianIntegralProcess hB f s | brownianNaturalFiltration B hBm s] ω = 0
  rw [ht, hs, sub_self]

theorem brownianStochasticIntegralProcess_increment_isometry (f : BrownianIntegrand)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (brownianStochasticIntegralProcess f t ω - brownianStochasticIntegralProcess f s ω) ^ 2
      ∂brownianDyadicMeasure) =
      ∫ p in brownianTimeWindow s t,
        (f : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) p ^ 2
          ∂volume.prod brownianDyadicMeasure :=
  brownianIntegralProcess_increment_isometry brownianDyadicPath_isPreBrownianReal f hst

end TimeTraps.Probability
