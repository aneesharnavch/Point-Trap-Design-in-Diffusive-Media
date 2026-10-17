module

public import TimeTraps.Probability.BrownianLocalTimeContinuousPath
public import TimeTraps.Probability.BrownianTanakaCompensationMonotone

@[expose] public section

/-! One measurable full-measure event supports continuous, nonnegative,
nondecreasing Tanaka candidate paths on a fixed compact time interval.
Only countably many fixed-time compensation comparisons are intersected;
the remaining times follow by continuity. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal ENNReal

def brownianLocalTimeRegular (a : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : Prop :=
  BrownianDyadicRegular ω ∧ brownianLocalTimeCandidate a T 0 ω = 0 ∧
    ∀ n m : ℕ,
      brownianLocalTimeCandidate a T
          (min (denseSeq (BrownianCompactTime T) n).val (denseSeq (BrownianCompactTime T) m).val) ω ≤
        brownianLocalTimeCandidate a T
          (max (denseSeq (BrownianCompactTime T) n).val (denseSeq (BrownianCompactTime T) m).val) ω

theorem brownianLocalTimeRegular_measurableSet (a : ℝ) (T : ℝ≥0) :
    MeasurableSet {ω | brownianLocalTimeRegular a T ω} := by
  have hc (t : ℝ≥0) : Measurable (brownianLocalTimeCandidate a T t) := by
    change Measurable (fun ω => |brownianDyadicPath t ω - a| - |brownianDyadicPath 0 ω - a| -
      brownianIntegralGlobalPath (brownianDyadicSignIntegrand a T) t ω)
    exact (((brownianDyadicPath_measurable t).sub_const a).abs.sub
      ((brownianDyadicPath_measurable 0).sub_const a).abs).sub
        (brownianIntegralGlobalPath_measurable (brownianDyadicSignIntegrand a T) t)
  let S : ℕ → ℕ → Set (ℕ → ℝ) := fun n m => {ω |
    brownianLocalTimeCandidate a T
        (min (denseSeq (BrownianCompactTime T) n).val (denseSeq (BrownianCompactTime T) m).val) ω ≤
      brownianLocalTimeCandidate a T
        (max (denseSeq (BrownianCompactTime T) n).val (denseSeq (BrownianCompactTime T) m).val) ω}
  have hS (n m : ℕ) : MeasurableSet (S n m) := measurableSet_le (hc _) (hc _)
  have he : {ω | brownianLocalTimeRegular a T ω} =
      {ω | BrownianDyadicRegular ω} ∩
        ({ω | brownianLocalTimeCandidate a T 0 ω = 0} ∩ ⋂ n, ⋂ m, S n m) := by
    ext ω
    simp only [brownianLocalTimeRegular, mem_inter_iff, mem_iInter, mem_ofPred_eq, S]
  rw [he]
  exact brownianDyadicRegular_measurableSet.inter
    ((measurableSet_eq_fun (hc 0) measurable_const).inter
      (MeasurableSet.iInter (fun n => MeasurableSet.iInter (hS n))))

theorem brownianLocalTimeCandidate_zero_ae (a : ℝ) (T : ℝ≥0) :
    brownianLocalTimeCandidate a T 0 =ᵐ[brownianDyadicMeasure] 0 := by
  have h := brownianLocalTimeCandidate_compensation_ae a (T := T) (t := 0) zero_le
  rw [brownianTanakaCompensation_zero] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 brownianDyadicMeasure)

theorem brownianLocalTimeRegular_ae (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, brownianLocalTimeRegular a T ω := by
  have hm : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n m : ℕ,
      brownianLocalTimeCandidate a T
          (min (denseSeq (BrownianCompactTime T) n).val (denseSeq (BrownianCompactTime T) m).val) ω ≤
        brownianLocalTimeCandidate a T
          (max (denseSeq (BrownianCompactTime T) n).val (denseSeq (BrownianCompactTime T) m).val) ω := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro m
    let s := (denseSeq (BrownianCompactTime T) n).val
    let t := (denseSeq (BrownianCompactTime T) m).val
    have hs : s ≤ T := (denseSeq (BrownianCompactTime T) n).property.2
    have ht : t ≤ T := (denseSeq (BrownianCompactTime T) m).property.2
    filter_upwards [brownianLocalTimeCandidate_compensation_ae a ((min_le_left s t).trans hs),
      brownianLocalTimeCandidate_compensation_ae a (max_le hs ht),
      brownianTanakaCompensation_mono brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable a (min_le_max : min s t ≤ max s t)] with ω hmin hmax hle
    change brownianLocalTimeCandidate a T (min s t) ω ≤ brownianLocalTimeCandidate a T (max s t) ω
    rw [hmin, hmax]
    exact hle
  filter_upwards [brownianDyadic_regular_ae, brownianLocalTimeCandidate_zero_ae a T, hm] with ω hr hzero hmono
  exact ⟨hr, hzero, hmono⟩

theorem brownianLocalTimeRegular_monotoneOn {a : ℝ} {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeRegular a T ω) :
    MonotoneOn (fun t => brownianLocalTimeCandidate a T t ω) (Icc (0 : ℝ≥0) T) := by
  have hc := brownianLocalTimeCandidate_continuous a T hω.1.continuous
  have hall : ∀ s t : BrownianCompactTime T,
      brownianLocalTimeCandidate a T (min s.val t.val) ω ≤
        brownianLocalTimeCandidate a T (max s.val t.val) ω := by
    apply isClosed_property2 (p := fun s t : BrownianCompactTime T =>
      brownianLocalTimeCandidate a T (min s.val t.val) ω ≤
        brownianLocalTimeCandidate a T (max s.val t.val) ω)
      (denseRange_denseSeq (BrownianCompactTime T))
    · exact isClosed_le
        (hc.comp ((continuous_subtype_val.comp continuous_fst).min
          (continuous_subtype_val.comp continuous_snd)))
        (hc.comp ((continuous_subtype_val.comp continuous_fst).max
          (continuous_subtype_val.comp continuous_snd)))
    · exact hω.2.2
  intro s hs t ht hst
  have h := hall ⟨s, hs⟩ ⟨t, ht⟩
  simpa only [min_eq_left hst, max_eq_right hst] using h

theorem brownianLocalTimeRegular_nonneg {a : ℝ} {T t : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeRegular a T ω) (ht : t ≤ T) :
    0 ≤ brownianLocalTimeCandidate a T t ω := by
  have h := brownianLocalTimeRegular_monotoneOn hω ⟨le_rfl, zero_le⟩ ⟨zero_le, ht⟩ zero_le
  change brownianLocalTimeCandidate a T 0 ω ≤ brownianLocalTimeCandidate a T t ω at h
  rw [hω.2.1] at h
  exact h

theorem brownianLocalTimeCandidate_regular_ae (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Continuous (fun t => brownianLocalTimeCandidate a T t ω) ∧
      MonotoneOn (fun t => brownianLocalTimeCandidate a T t ω) (Icc (0 : ℝ≥0) T) ∧
      brownianLocalTimeCandidate a T 0 ω = 0 ∧
      ∀ t ∈ Icc (0 : ℝ≥0) T, 0 ≤ brownianLocalTimeCandidate a T t ω := by
  filter_upwards [brownianLocalTimeRegular_ae a T] with ω hω
  exact ⟨brownianLocalTimeCandidate_continuous a T hω.1.continuous,
    brownianLocalTimeRegular_monotoneOn hω, hω.2.1,
    fun _ ht => brownianLocalTimeRegular_nonneg hω ht.2⟩

end TimeTraps.Probability

end
