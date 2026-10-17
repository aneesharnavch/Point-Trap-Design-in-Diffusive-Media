module

public import TimeTraps.Probability.BrownianIntegralTruncationSpaces

@[expose] public section

/-! Deterministic cutoff algebra on the completed integrand domain. Nested
cutoffs take the smaller time, and the cutoff at zero vanishes. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

theorem brownianTimePast_inter (s t : ℝ≥0) :
    brownianTimePast (Ω := Ω) s ∩ brownianTimePast t = brownianTimePast (min s t) := by
  ext p
  change (p.1 ≤ s.val ∧ p.1 ≤ t.val) ↔ p.1 ≤ min s.val t.val
  exact le_min_iff.symm

theorem brownianTimeCutoff_comp (s t : ℝ≥0) (f : brownianIntegralSpace B hBm P) :
    brownianTimeCutoff B hBm P s (brownianTimeCutoff B hBm P t f) =
      brownianTimeCutoff B hBm P (min s t) f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [brownianTimeCutoff_coe s (brownianTimeCutoff B hBm P t f),
    brownianTimeCutoff_coe t f, brownianTimeCutoff_coe (min s t) f] with p hout hin hmin
  rw [hout, hmin]
  have he : (brownianTimePast s).indicator
      (brownianTimeCutoff B hBm P t f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p =
      (brownianTimePast s).indicator ((brownianTimePast t).indicator
        (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))) p := by
    by_cases hp : p ∈ brownianTimePast s
    · simp only [indicator_of_mem hp]
      exact hin
    · simp only [indicator_of_notMem hp]
  rw [he, indicator_indicator, brownianTimePast_inter]

theorem brownianTimeCutoff_of_le {s t : ℝ≥0} (hst : s ≤ t) (f : brownianIntegralSpace B hBm P) :
    brownianTimeCutoff B hBm P s (brownianTimeCutoff B hBm P t f) =
      brownianTimeCutoff B hBm P s f := by
  rw [brownianTimeCutoff_comp, min_eq_left hst]

theorem brownianTimeCutoff_zero (f : brownianIntegralSpace B hBm P) :
    brownianTimeCutoff B hBm P 0 f = 0 := by
  apply brownianIntegralSpace_mem_of_generators (brownianTimeCutoff B hBm P 0).ker
    (brownianTimeCutoff B hBm P 0).isClosed_ker _ f
  intro a
  exact brownianTimeCutoff_generator_zero a zero_le

end TimeTraps.Probability
