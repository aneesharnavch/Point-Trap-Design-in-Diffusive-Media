module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovPathData
public import TimeTraps.Analysis.PositiveTimeChangeCompact
public import TimeTraps.Probability.ReflectedC2ItoDriftMeasurable

@[expose] public section

/-! The literal positive clock and its inverse are measurable functionals
of a compact continuous path. Constant continuation after the horizon
makes every path admissible; prefix agreement will remove that continuation
whenever the sampled reference time lies within the horizon. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal

def reflectedMarkovPathExtend (L : ℝ) (H : ℝ≥0) (p : ReflectedMarkovPath L H)
    (s : ℝ≥0) : Icc (0 : ℝ) L :=
  p ⟨min s H, bot_le, min_le_right s H⟩

theorem reflectedMarkovPathExtend_joint_continuous (L : ℝ) (H : ℝ≥0) :
    Continuous (fun q : ℝ≥0 × ReflectedMarkovPath L H => reflectedMarkovPathExtend L H q.2 q.1) :=
  continuous_eval.comp (continuous_snd.prodMk
    ((continuous_fst.min continuous_const).subtype_mk _))

def reflectedMarkovPathSpeed (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y)
    (p : ReflectedMarkovPath L H) : PositiveTimeSpeed := by
  let : Nonempty (Icc (0 : ℝ) L) := ⟨⟨0, le_rfl, hL.le⟩⟩
  exact PositiveTimeSpeed.ofCompact c hc hpos (reflectedMarkovPathExtend L H p)
    ((reflectedMarkovPathExtend_joint_continuous L H).comp (continuous_id.prodMk continuous_const))

theorem reflectedMarkovPathSpeed_rate (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y)
    (p : ReflectedMarkovPath L H) (s : ℝ≥0) :
    (reflectedMarkovPathSpeed L hL H c hc hpos p).rate s =
      c (reflectedMarkovPathExtend L H p s) := rfl

theorem reflectedMarkovPathSpeed_clock_measurable (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y) :
    Measurable (fun q : ℝ≥0 × ReflectedMarkovPath L H =>
      (reflectedMarkovPathSpeed L hL H c hc hpos q.2).clock q.1) := by
  have hm : Measurable (fun q : ℝ × ReflectedMarkovPath L H =>
      c (reflectedMarkovPathExtend L H q.2 q.1.toNNReal)) :=
    hc.measurable.comp ((reflectedMarkovPathExtend_joint_continuous L H).measurable.comp
      (measurable_fst.real_toNNReal.prodMk measurable_snd))
  apply measurable_coe_nnreal_real_iff.mp
  exact timeIntegral_jointlyMeasurable hm

theorem reflectedMarkovPathSpeed_inverse_le_iff (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y)
    (p : ReflectedMarkovPath L H) (t s : ℝ≥0) :
    (reflectedMarkovPathSpeed L hL H c hc hpos p).inverse t ≤ s ↔
      t ≤ (reflectedMarkovPathSpeed L hL H c hc hpos p).clock s := by
  let v := reflectedMarkovPathSpeed L hL H c hc hpos p
  change v.inverse t ≤ s ↔ t ≤ v.clock s
  constructor
  · intro h
    simpa only [v.clock_inverse] using v.clock_strictMono.monotone h
  · intro h
    apply v.clock_strictMono.le_iff_le.mp
    simpa only [v.clock_inverse] using h

theorem reflectedMarkovPathSpeed_inverse_measurable (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y) :
    Measurable (fun q : ℝ≥0 × ReflectedMarkovPath L H =>
      (reflectedMarkovPathSpeed L hL H c hc hpos q.2).inverse q.1) := by
  apply measurable_of_Iic
  intro s
  have he : (fun q : ℝ≥0 × ReflectedMarkovPath L H =>
      (reflectedMarkovPathSpeed L hL H c hc hpos q.2).inverse q.1) ⁻¹' Iic s =
      {q | q.1 ≤ (reflectedMarkovPathSpeed L hL H c hc hpos q.2).clock s} := by
    ext q
    exact reflectedMarkovPathSpeed_inverse_le_iff L hL H c hc hpos q.2 q.1 s
  rw [he]
  exact measurableSet_le measurable_fst
    ((reflectedMarkovPathSpeed_clock_measurable L hL H c hc hpos).comp
      (measurable_const.prodMk measurable_snd))

def reflectedMarkovPathTimeChange (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y)
    (t : ℝ≥0) (p : ReflectedMarkovPath L H) : Icc (0 : ℝ) L :=
  reflectedMarkovPathExtend L H p ((reflectedMarkovPathSpeed L hL H c hc hpos p).inverse t)

theorem reflectedMarkovPathTimeChange_measurable (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y) (t : ℝ≥0) :
    Measurable (reflectedMarkovPathTimeChange L hL H c hc hpos t) :=
  (reflectedMarkovPathExtend_joint_continuous L H).measurable.comp
    (((reflectedMarkovPathSpeed_inverse_measurable L hL H c hc hpos).comp
      (measurable_const.prodMk measurable_id)).prodMk measurable_id)

end TimeTraps.Probability

end
