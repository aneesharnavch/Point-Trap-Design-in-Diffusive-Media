module

public import TimeTraps.Probability.ContinuousPathLocalTimeData

@[expose] public section

/-! The canonical good-path set is stable under every nonnegative time
shift. On that set the occupation-band limit is a continuous increasing
additive functional. All shift identities are derived from the literal
band integrals before taking their compact-time limits. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal Topology

theorem continuousPathOccupationBand_shift_tendsto (a : ℝ) (m : ℝ → ℝ)
    (p l : ReversibleNeumannFullPath) (s : ℝ≥0)
    (h : Tendsto (fun n => continuousPathOccupationBand a (occupationBandRadius n)
      (m (occupationBandRadius n)) p) atTop (𝓝 l)) :
    Tendsto (fun n => continuousPathOccupationBand a (occupationBandRadius n)
      (m (occupationBandRadius n)) (continuousPathShift s p)) atTop
        (𝓝 (continuousPathShift s l - ContinuousMap.const ℝ≥0 (l s))) := by
  have hc : Continuous (fun q : ReversibleNeumannFullPath =>
      continuousPathShift s q - ContinuousMap.const ℝ≥0 (q s)) :=
    (continuousPathShift_continuous s).sub
      (ContinuousMap.continuous_const'.comp (continuous_eval_const s))
  simpa only [continuousPathOccupationBand_shift, Function.comp_def] using hc.continuousAt.tendsto.comp h

theorem HasContinuousOccupationLocalTime.shift {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p) (s : ℝ≥0) :
    HasContinuousOccupationLocalTime a m (continuousPathShift s p) :=
  ⟨_, continuousPathOccupationBand_shift_tendsto a m p (continuousPathLocalTime a m p) s h.tendsto⟩

theorem HasContinuousOccupationLocalTime.shift_eq {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p) (s : ℝ≥0) :
    continuousPathLocalTime a m (continuousPathShift s p) =
      continuousPathShift s (continuousPathLocalTime a m p) -
        ContinuousMap.const ℝ≥0 (continuousPathLocalTime a m p s) :=
  continuousPathLocalTime_eq_of_tendsto a m (continuousPathShift s p) _
    (continuousPathOccupationBand_shift_tendsto a m p (continuousPathLocalTime a m p) s h.tendsto)

theorem HasContinuousOccupationLocalTime.cocycle {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p) (s t : ℝ≥0) :
    continuousPathLocalTime a m p (s + t) = continuousPathLocalTime a m p s +
      continuousPathLocalTime a m (continuousPathShift s p) t := by
  have he := congrArg (fun q : ReversibleNeumannFullPath => q t) (h.shift_eq s)
  change continuousPathLocalTime a m (continuousPathShift s p) t =
    continuousPathLocalTime a m p (s + t) - continuousPathLocalTime a m p s at he
  linarith

theorem HasContinuousOccupationLocalTime.zero {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p) :
    continuousPathLocalTime a m p 0 = 0 := by
  have hz := h.eval_tendsto 0
  simp only [continuousPathOccupationBand_zero] at hz
  exact tendsto_nhds_unique hz tendsto_const_nhds

theorem HasContinuousOccupationLocalTime.monotone {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p)
    (hm : ∀ r, 0 < r → 0 ≤ m r) : Monotone (continuousPathLocalTime a m p) := by
  intro s t hst
  exact le_of_tendsto_of_tendsto (h.eval_tendsto s) (h.eval_tendsto t)
    (Eventually.of_forall (fun n => continuousPathOccupationBand_monotone a
      (occupationBandRadius n) (m (occupationBandRadius n))
      (hm _ (occupationBandRadius_pos n)) p hst))

theorem HasContinuousOccupationLocalTime.nonneg {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p)
    (hm : ∀ r, 0 < r → 0 ≤ m r) (t : ℝ≥0) : 0 ≤ continuousPathLocalTime a m p t := by
  rw [← h.zero]
  exact h.monotone hm t.property

end TimeTraps.Probability

end
