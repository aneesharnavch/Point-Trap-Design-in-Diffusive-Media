module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovPathClockData
public import TimeTraps.Analysis.PositiveTimeChangeFamilyContinuity

@[expose] public section

/-! The literal clock, inverse and sampled state depend continuously
on the compact reference path. No stochastic continuity or Feller
property is used to obtain these deterministic facts. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped NNReal

theorem reflectedMarkovPathSpeed_clock_continuous_path (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y) (s : ℝ≥0) :
    Continuous (fun p : ReflectedMarkovPath L H =>
      (reflectedMarkovPathSpeed L hL H c hc hpos p).clock s) := by
  have hj : Continuous (fun q : ReflectedMarkovPath L H × ℝ =>
      c (reflectedMarkovPathExtend L H q.1 q.2.toNNReal)) :=
    hc.comp ((reflectedMarkovPathExtend_joint_continuous L H).comp
      ((continuous_real_toNNReal.comp continuous_snd).prodMk continuous_fst))
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hj 0 s.val).subtype_mk _

theorem reflectedMarkovPathSpeed_inverse_joint_continuous (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y) :
    Continuous (fun q : ℝ≥0 × ReflectedMarkovPath L H =>
      (reflectedMarkovPathSpeed L hL H c hc hpos q.2).inverse q.1) :=
  positiveTimeSpeed_family_inverse_continuous _
    (reflectedMarkovPathSpeed_clock_continuous_path L hL H c hc hpos)

theorem reflectedMarkovPathTimeChange_joint_continuous (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y) :
    Continuous (fun q : ℝ≥0 × ReflectedMarkovPath L H =>
      reflectedMarkovPathTimeChange L hL H c hc hpos q.1 q.2) :=
  (reflectedMarkovPathExtend_joint_continuous L H).comp
    ((reflectedMarkovPathSpeed_inverse_joint_continuous L hL H c hc hpos).prodMk continuous_snd)

end TimeTraps.Probability

end
