module

public import TimeTraps.Probability.BrownianLocalTimeJointContinuity
public import TimeTraps.Probability.BrownianLocalTimeLevelVersion

@[expose] public section

/-! One nonnegative jointly measurable field of level, time and outcome
represents the actual Tanaka compensation at every fixed parameter pair.
This is a measurable version assertion, not sample-path continuity in
either parameter or a common uncountable-parameter equality event. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def brownianLocalTimeJointVersion (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  max 0 (l2FamilyMeasurableVersion
    (brownianTanakaCompensation_joint_continuous hB hBm hjoint).stronglyMeasurable (a, T) ω)

theorem brownianLocalTimeJointVersion_jointlyMeasurable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) :
    Measurable (fun p : (ℝ × ℝ≥0) × Ω => brownianLocalTimeJointVersion hB hBm hjoint p.1.1 p.1.2 p.2) :=
  measurable_const.max (l2FamilyMeasurableVersion_jointlyMeasurable
    (brownianTanakaCompensation_joint_continuous hB hBm hjoint).stronglyMeasurable)

theorem brownianLocalTimeJointVersion_timeSlice_measurable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Measurable (fun p : ℝ × Ω => brownianLocalTimeJointVersion hB hBm hjoint p.1 T p.2) := by
  let φ : ℝ × Ω → (ℝ × ℝ≥0) × Ω := fun p => ((p.1, T), p.2)
  have hφ : Measurable φ := (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hm := (brownianLocalTimeJointVersion_jointlyMeasurable hB hBm hjoint).comp hφ
  change Measurable (fun p : ℝ × Ω => brownianLocalTimeJointVersion hB hBm hjoint p.1 T p.2) at hm
  exact hm

theorem brownianLocalTimeJointVersion_nonneg (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (ω : Ω) :
    0 ≤ brownianLocalTimeJointVersion hB hBm hjoint a T ω := le_max_left _ _

theorem brownianLocalTimeJointVersion_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    brownianLocalTimeJointVersion hB hBm hjoint a T =ᵐ[P]
      brownianTanakaCompensation hB hBm hjoint a T := by
  filter_upwards [l2FamilyMeasurableVersion_ae
    (brownianTanakaCompensation_joint_continuous hB hBm hjoint).stronglyMeasurable (a, T),
    brownianTanakaCompensation_nonneg hB hBm hjoint a T] with ω he hn
  change max 0 _ = _
  rw [he, max_eq_right hn]

theorem brownianLocalTimeJointVersion_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    MemLp (brownianLocalTimeJointVersion hB hBm hjoint a T) 2 P :=
  (memLp_congr_ae (brownianLocalTimeJointVersion_ae hB hBm hjoint a T)).mpr
    (Lp.memLp (brownianTanakaCompensation hB hBm hjoint a T))

theorem brownianLocalTimeJointVersion_toLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    (brownianLocalTimeJointVersion_memLp hB hBm hjoint a T).toLp
      (brownianLocalTimeJointVersion hB hBm hjoint a T) =
        brownianTanakaCompensation hB hBm hjoint a T := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp (brownianLocalTimeJointVersion_memLp hB hBm hjoint a T)).trans
    (brownianLocalTimeJointVersion_ae hB hBm hjoint a T)

theorem brownianLocalTimeJointVersion_levelVersion_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    brownianLocalTimeJointVersion hB hBm hjoint a T =ᵐ[P]
      brownianLocalTimeLevelVersion hB hBm hjoint T a :=
  (brownianLocalTimeJointVersion_ae hB hBm hjoint a T).trans
    (brownianLocalTimeLevelVersion_ae hB hBm hjoint T a).symm

def brownianDyadicLocalTimeJointVersion : ℝ → ℝ≥0 → (ℕ → ℝ) → ℝ :=
  brownianLocalTimeJointVersion brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable

theorem brownianDyadicLocalTimeJointVersion_globalPath_ae (a : ℝ) (T : ℝ≥0) :
    brownianDyadicLocalTimeJointVersion a T =ᵐ[brownianDyadicMeasure] brownianLocalTimeGlobalPath a T :=
  (brownianLocalTimeJointVersion_ae brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a T).trans (brownianLocalTimeGlobalPath_compensation_ae a T).symm

end TimeTraps.Probability

end
