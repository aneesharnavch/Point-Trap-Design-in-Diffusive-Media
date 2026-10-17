module

public import TimeTraps.Probability.OccupationProductTime

@[expose] public section

/-! The strict ordered-square integral is the conventional upper-triangle
integral. Variable lower limits are justified by the literal restricted
Lebesgue measures, without an assumed Fubini identity. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter

theorem chronological_interval_section (J : ℝ → ℝ) {s T : ℝ}
    (hs : 0 ≤ s) (hsT : s ≤ T) :
    (∫ t in Ioc 0 T, if s < t then J t else 0) = ∫ t in s..T, J t := by
  have he : Ioi s ∩ Ioc 0 T = Ioc s T := by
    ext t
    constructor
    · rintro ⟨ht, hT⟩
      exact ⟨ht, hT.2⟩
    · intro ht
      exact ⟨ht.1, ⟨hs.trans_lt ht.1, ht.2⟩⟩
  calc
    _ = ∫ t in Ioi s, J t ∂volume.restrict (Ioc 0 T) :=
      integral_indicator measurableSet_Ioi
    _ = ∫ t in Ioc s T, J t := by rw [Measure.restrict_restrict measurableSet_Ioi, he]
    _ = _ := (intervalIntegral.integral_of_le hsT).symm

theorem orderedTimeIntegral_eq_upperTriangle (H : ℝ × ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hi : Integrable (fun p => if p.1 < p.2 then H p else 0)
      ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T)))) :
    orderedTimeIntegral (volume.restrict (Ioc 0 T)) H =
      ∫ s in 0..T, ∫ t in s..T, H (s, t) := by
  calc
    _ = ∫ s in Ioc 0 T, ∫ t in Ioc 0 T, if s < t then H (s, t) else 0 := integral_prod _ hi
    _ = ∫ s in Ioc 0 T, ∫ t in s..T, H (s, t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact chronological_interval_section (fun t => H (s, t)) hs.1.le hs.2
    _ = _ := (intervalIntegral.integral_of_le hT).symm

end TimeTraps.Probability
