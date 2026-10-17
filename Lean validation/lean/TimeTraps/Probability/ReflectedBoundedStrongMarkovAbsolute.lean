module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovCylinder
public import TimeTraps.Probability.ReflectedBoundedStrongMarkovBorelData
public import Mathlib.Data.List.Sort

@[expose] public section

/-! Continuous finite products at arbitrary, possibly repeated future
times. Sorting only reorders multiplication; nonnegative time differences
then reduce their conditional law to the proved chronological cylinders. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

def reflectedMarkovAbsoluteCylinder (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (w : ReflectedMarkovWord L) (t : ℝ≥0) (ω : BrownianCompletedSample) : ℝ :=
  (w.map (fun a => reflectedMarkovObservation L hL D x a.2 (t + a.1) ω)).prod

def reflectedMarkovDurations {L : ℝ} : ℝ≥0 → ReflectedMarkovWord L → ReflectedMarkovWord L
  | _, [] => []
  | s, (t, f) :: w => (t - s, f) :: reflectedMarkovDurations t w

def reflectedMarkovTimeSort {L : ℝ} (w : ReflectedMarkovWord L) : ReflectedMarkovWord L :=
  w.mergeSort (fun a b => a.1 ≤ b.1)

theorem reflectedMarkovTimeSort_pairwise {L : ℝ} (w : ReflectedMarkovWord L) :
    (reflectedMarkovTimeSort w).Pairwise (fun a b => a.1 ≤ b.1) := by
  simpa only [reflectedMarkovTimeSort, decide_eq_true_eq] using
    (List.pairwise_mergeSort (le := fun a b : ℝ≥0 × C(Icc (0 : ℝ) L, ℝ) => a.1 ≤ b.1)
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hab hbc)
      (fun a b => by simpa using le_total a.1 b.1) w)

theorem reflectedMarkovDurations_cylinder (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (w : ReflectedMarkovWord L) (s : ℝ≥0)
    (hw : w.Pairwise (fun a b => a.1 ≤ b.1)) (hs : ∀ a ∈ w, s ≤ a.1)
    (t : ℝ≥0) (ω : BrownianCompletedSample) :
    reflectedMarkovCylinder L hL D x (reflectedMarkovDurations s w) (t + s) ω =
      reflectedMarkovAbsoluteCylinder L hL D x w t ω := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
      rcases a with ⟨r, f⟩
      have hsr : s ≤ r := hs _ List.mem_cons_self
      have hsum : t + s + (r - s) = t + r := by
        rw [add_assoc, add_tsub_cancel_of_le hsr]
      simp only [reflectedMarkovDurations, reflectedMarkovCylinder, hsum]
      rw [ih r hw.tail (List.pairwise_cons.mp hw).1]
      rfl

theorem reflectedMarkovAbsoluteCylinder_sorted (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (w : ReflectedMarkovWord L) (t : ℝ≥0) (ω : BrownianCompletedSample) :
    reflectedMarkovAbsoluteCylinder L hL D x w t ω =
      reflectedMarkovCylinder L hL D x (reflectedMarkovDurations 0 (reflectedMarkovTimeSort w)) t ω := by
  have he := reflectedMarkovDurations_cylinder L hL D x (reflectedMarkovTimeSort w) 0
    (reflectedMarkovTimeSort_pairwise w) (fun _ _ => bot_le) t ω
  simp only [add_zero] at he
  rw [he]
  exact ((List.mergeSort_perm w (fun a b => a.1 ≤ b.1)).map
    (fun a => reflectedMarkovObservation L hL D x a.2 (t + a.1) ω)).prod_eq.symm

def reflectedMarkovAbsoluteKernel (L : ℝ) (hL : 0 < L) (D : ℝ) (w : ReflectedMarkovWord L) :
    C(Icc (0 : ℝ) L, ℝ) :=
  reflectedMarkovCylinderKernel L hL D (reflectedMarkovDurations 0 (reflectedMarkovTimeSort w))

theorem reflectedMarkovAbsoluteCylinder_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (w : ReflectedMarkovWord L)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => reflectedMarkovAbsoluteCylinder L hL D x w (τ ω) ω)
      brownianCompletedMeasure := by
  simpa only [reflectedMarkovAbsoluteCylinder_sorted] using
    reflectedMarkovCylinder_stopped_integrable L hL D x
      (reflectedMarkovDurations 0 (reflectedMarkovTimeSort w)) hτ

theorem reflectedMarkovAbsoluteCylinder_condExp
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (w : ReflectedMarkovWord L)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    brownianCompletedMeasure[(fun ω => reflectedMarkovAbsoluteCylinder L hL D x w (τ ω) ω) |
      hτ.measurableSpace] =ᵐ[brownianCompletedMeasure]
        (fun ω => reflectedMarkovObservation L hL D x (reflectedMarkovAbsoluteKernel L hL D w) (τ ω) ω) := by
  simpa only [reflectedMarkovAbsoluteCylinder_sorted, reflectedMarkovAbsoluteKernel] using
    reflectedMarkovCylinder_condExp L hL D hD x
      (reflectedMarkovDurations 0 (reflectedMarkovTimeSort w)) hτ

theorem reflectedMarkovState_zero_ae (L : ℝ) (hL : 0 < L) (D : ℝ) (y : Icc (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianCompletedMeasure, reflectedMarkovState L hL D y.val 0 ω = y := by
  have hz : ∀ᵐ ω ∂brownianCompletedMeasure, brownianDyadicPath 0 ω = 0 :=
    brownianDyadicPath_start_zero
  filter_upwards [reflectedMarkovBrownianPath_ae_all, hz] with ω hω hz
  apply Subtype.ext
  change reflectedFold L (y.val + Real.sqrt (2 * D) * reflectedMarkovBrownianPath 0 ω) = y.val
  rw [hω 0, hz, mul_zero, add_zero]
  exact reflectedFold_eq_self L hL y.val y.property

theorem reflectedMarkovAbsoluteCylinder_expectation (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (y : Icc (0 : ℝ) L) (w : ReflectedMarkovWord L) :
    ∫ ω, reflectedMarkovAbsoluteCylinder L hL D y.val w 0 ω ∂brownianCompletedMeasure =
      reflectedMarkovAbsoluteKernel L hL D w y := by
  have hτ := isStoppingTime_const brownianCompletedFiltration.rightCont (0 : ℝ≥0)
  have he := reflectedMarkovAbsoluteCylinder_condExp L hL D hD y.val w hτ
  calc
    _ = ∫ ω, reflectedMarkovObservation L hL D y.val
        (reflectedMarkovAbsoluteKernel L hL D w) 0 ω ∂brownianCompletedMeasure := by
      rw [← integral_condExp hτ.measurableSpace_le]
      exact integral_congr_ae he
    _ = ∫ _, reflectedMarkovAbsoluteKernel L hL D w y ∂brownianCompletedMeasure := by
      apply integral_congr_ae
      filter_upwards [reflectedMarkovState_zero_ae L hL D y] with ω hω
      exact congrArg (reflectedMarkovAbsoluteKernel L hL D w) hω
    _ = _ := by simp

end TimeTraps.Probability

end
