module

public import TimeTraps.Probability.BrownianLocalTimeSupportGlobal

@[expose] public section

/-! Continuity extends the already simultaneous rational-interval
flatness to arbitrary nonnegative real endpoints, on the same event. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

theorem nnreal_exists_nnrat_between {s t : ℝ≥0} (hst : s < t) :
    ∃ q : ℚ≥0, s < (q : ℝ≥0) ∧ (q : ℝ≥0) < t := by
  obtain ⟨q, hs, ht⟩ := exists_rat_btwn (show (s : ℝ) < (t : ℝ) from hst)
  have hq : 0 ≤ q := Rat.cast_nonneg.mp (s.property.trans hs.le)
  refine ⟨⟨q, hq⟩, ?_, ?_⟩
  · change (s : ℝ) < ((⟨q, hq⟩ : ℚ≥0) : ℝ)
    simpa only [NNRat.cast_mk] using hs
  · change ((⟨q, hq⟩ : ℚ≥0) : ℝ) < (t : ℝ)
    simpa only [NNRat.cast_mk] using ht

theorem continuous_flat_of_rational_intervals {f : ℝ≥0 → ℝ} (hf : Continuous f)
    {S T : ℝ≥0} (hST : S ≤ T)
    (hflat : ∀ p q : ℚ≥0, S ≤ (p : ℝ≥0) → (q : ℝ≥0) ≤ T →
      (p : ℝ≥0) ≤ (q : ℝ≥0) → ∀ s ∈ Icc (p : ℝ≥0) (q : ℝ≥0), f s = f p) :
    ∀ s ∈ Icc S T, f s = f S := by
  rcases hST.eq_or_lt with heq | hlt
  · subst T
    intro s hs
    exact congrArg f (le_antisymm hs.2 hs.1)
  obtain ⟨m, hSm, hmT⟩ := exists_between hlt
  have hi : EqOn f (fun _ => f m) (Ioo S T) := by
    intro s hs
    obtain ⟨p, hSp, hpm⟩ := nnreal_exists_nnrat_between (lt_min hs.1 hSm)
    obtain ⟨q, hmq, hqT⟩ := nnreal_exists_nnrat_between (max_lt hs.2 hmT)
    have hps : (p : ℝ≥0) < s := hpm.trans_le (min_le_left s m)
    have hpm' : (p : ℝ≥0) < m := hpm.trans_le (min_le_right s m)
    have hsq : s < (q : ℝ≥0) := (le_max_left s m).trans_lt hmq
    have hmq' : m < (q : ℝ≥0) := (le_max_right s m).trans_lt hmq
    have h := hflat p q hSp.le hqT.le (hps.trans hsq).le
    exact (h s ⟨hps.le, hsq.le⟩).trans (h m ⟨hpm'.le, hmq'.le⟩).symm
  have hc : EqOn f (fun _ => f m) (Icc S T) := by
    simpa only [closure_Ioo hlt.ne] using hi.closure hf continuous_const
  intro s hs
  exact (hc hs).trans (hc ⟨le_rfl, hST⟩).symm

theorem brownianLocalTimeSupportRegular_flat_real {a : ℝ} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeSupportRegular a ω) {S T : ℝ≥0} (hST : S ≤ T)
    {δ : ℝ} (hδ : 0 < δ)
    (haway : ∀ s ∈ Icc S T, δ ≤ |brownianDyadicPath s ω - a|) :
    ∀ s ∈ Icc S T, brownianLocalTimeGlobalPath a s ω = brownianLocalTimeGlobalPath a S ω := by
  apply continuous_flat_of_rational_intervals (brownianLocalTimeGlobalPath_continuous a ω) hST
  intro p q hp hq hpq
  exact brownianLocalTimeSupportRegular_flat hω p q hpq hδ (fun s hs =>
    haway s ⟨hp.trans hs.1, hs.2.trans hq⟩)

end TimeTraps.Probability
