module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovTimeChangeData
public import TimeTraps.Probability.ReflectedBoundedStrongMarkovPath

@[expose] public section

/-! The time-changed transition expectation is independently defined
from the literal inverse-clock trajectory. The finite-path functional
identifies it with a measurable continuation law on the physical interval. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal

def reflectedTimeChangedOperator (L D : ℝ) (c : ℝ → ℝ) (t : ℝ≥0)
    (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ ω, f (reflectedTimeChangedTrajectory L D y c t ω) ∂brownianCompletedMeasure

def reflectedTimeChangedPathTest (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) (f : ℝ → ℝ) (p : ReflectedMarkovPath L H) : ℝ :=
  f (reflectedMarkovPathTimeChange L hL H (fun y : Icc (0 : ℝ) L => c y.val)
    hc.domRestrict (fun y => hpos y.val y.property) t p).val

theorem reflectedTimeChangedPathTest_measurable (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (reflectedTimeChangedPathTest L hL H c hc hpos t f) :=
  hf.comp (measurable_subtype_coe.comp
    (reflectedMarkovPathTimeChange_measurable L hL H (fun y : Icc (0 : ℝ) L => c y.val)
      hc.domRestrict (fun y => hpos y.val y.property) t))

theorem reflectedTimeChangedOperator_path (L : ℝ) (hL : 0 < L) (D : ℝ) (H : ℝ≥0)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y)
    (t : ℝ≥0) (ht : t / m ≤ H) (f : ℝ → ℝ) (y : Icc (0 : ℝ) L) :
    reflectedMarkovPathOperator L hL D H (reflectedTimeChangedPathTest L hL H c hc hpos t f) y =
      reflectedTimeChangedOperator L D c t f y.val := by
  apply integral_congr_ae
  filter_upwards [reflectedMarkovPathTimeChange_fresh_actual L hL D H c hc hpos m hm hmc t ht y]
    with ω hω
  exact congrArg f hω

theorem reflectedTimeChangedOperator_measurable_interval (L : ℝ) (hL : 0 < L) (D : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun y : Icc (0 : ℝ) L => reflectedTimeChangedOperator L D c t f y.val) := by
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.le⟩) hc
  let m : ℝ≥0 := ⟨c a, (hpos a ha).le⟩
  have hm : 0 < m := hpos a ha
  have hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y := fun y hy => hmin hy
  have he : (fun y : Icc (0 : ℝ) L => reflectedTimeChangedOperator L D c t f y.val) =
      reflectedMarkovPathOperator L hL D (t / m)
        (reflectedTimeChangedPathTest L hL (t / m) c hc hpos t f) := by
    funext y
    exact (reflectedTimeChangedOperator_path L hL D (t / m) c hc hpos m hm hmc t le_rfl f y).symm
  rw [he]
  exact reflectedMarkovPathOperator_measurable L hL D (t / m)
    (reflectedTimeChangedPathTest_measurable L hL (t / m) c hc hpos t hf)

theorem reflectedTimeChangedOperator_bound (L D : ℝ) (c : ℝ → ℝ) (t : ℝ≥0)
    {f : ℝ → ℝ} {M : ℝ} (hb : ∀ y, |f y| ≤ M) (y : ℝ) :
    |reflectedTimeChangedOperator L D c t f y| ≤ M := by
  simpa only [reflectedTimeChangedOperator, Real.norm_eq_abs, MeasureTheory.probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := brownianCompletedMeasure)
      (f := fun ω => f (reflectedTimeChangedTrajectory L D y c t ω)) (C := M)
      (Eventually.of_forall (fun ω => hb _)))

end TimeTraps.Probability

end
