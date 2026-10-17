module

public import TimeTraps.Analysis.L2FamilyMeasurableVersion
public import TimeTraps.Probability.BrownianLocalTimeLevelCompensation
public import TimeTraps.Probability.BrownianLocalTimeGlobal

@[expose] public section

/-! At a fixed finite time, the actual Tanaka compensation has a
jointly measurable, nonnegative representative in level and sample.
It agrees with the actual L² class at every fixed level, and with the
constructed global local-time path at every fixed level and time.
No spatial path continuity or common exceptional set in level is used. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def brownianLocalTimeLevelVersion (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (a : ℝ) (ω : Ω) : ℝ :=
  max 0 (l2FamilyMeasurableVersion
    (brownianTanakaCompensation_level_continuous hB hBm hjoint T).stronglyMeasurable a ω)

theorem brownianLocalTimeLevelVersion_jointlyMeasurable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Measurable (fun p : ℝ × Ω => brownianLocalTimeLevelVersion hB hBm hjoint T p.1 p.2) :=
  measurable_const.max (l2FamilyMeasurableVersion_jointlyMeasurable
    (brownianTanakaCompensation_level_continuous hB hBm hjoint T).stronglyMeasurable)

theorem brownianLocalTimeLevelVersion_nonneg (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (a : ℝ) (ω : Ω) :
    0 ≤ brownianLocalTimeLevelVersion hB hBm hjoint T a ω :=
  le_max_left _ _

theorem brownianLocalTimeLevelVersion_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (a : ℝ) :
    brownianLocalTimeLevelVersion hB hBm hjoint T a =ᵐ[P]
      brownianTanakaCompensation hB hBm hjoint a T := by
  filter_upwards [l2FamilyMeasurableVersion_ae
    (brownianTanakaCompensation_level_continuous hB hBm hjoint T).stronglyMeasurable a,
    brownianTanakaCompensation_nonneg hB hBm hjoint a T] with ω he hn
  change max 0 _ = _
  rw [he, max_eq_right hn]

theorem brownianLocalTimeLevelVersion_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (a : ℝ) :
    MemLp (brownianLocalTimeLevelVersion hB hBm hjoint T a) 2 P :=
  (memLp_congr_ae (brownianLocalTimeLevelVersion_ae hB hBm hjoint T a)).mpr
    (Lp.memLp (brownianTanakaCompensation hB hBm hjoint a T))

theorem brownianLocalTimeLevelVersion_toLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (a : ℝ) :
    (brownianLocalTimeLevelVersion_memLp hB hBm hjoint T a).toLp
      (brownianLocalTimeLevelVersion hB hBm hjoint T a) =
        brownianTanakaCompensation hB hBm hjoint a T := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp (brownianLocalTimeLevelVersion_memLp hB hBm hjoint T a)).trans
    (brownianLocalTimeLevelVersion_ae hB hBm hjoint T a)

def brownianDyadicLocalTimeLevelVersion (T : ℝ≥0) : ℝ → (ℕ → ℝ) → ℝ :=
  brownianLocalTimeLevelVersion brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T

theorem brownianDyadicLocalTimeLevelVersion_jointlyMeasurable (T : ℝ≥0) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => brownianDyadicLocalTimeLevelVersion T p.1 p.2) :=
  brownianLocalTimeLevelVersion_jointlyMeasurable brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable T

theorem brownianDyadicLocalTimeLevelVersion_globalPath_ae (T : ℝ≥0) (a : ℝ) :
    brownianDyadicLocalTimeLevelVersion T a =ᵐ[brownianDyadicMeasure] brownianLocalTimeGlobalPath a T :=
  (brownianLocalTimeLevelVersion_ae brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T a).trans (brownianLocalTimeGlobalPath_compensation_ae a T).symm

end TimeTraps.Probability

end
