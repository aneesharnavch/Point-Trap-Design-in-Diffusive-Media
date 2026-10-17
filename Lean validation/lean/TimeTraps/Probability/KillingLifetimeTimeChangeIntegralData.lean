module

public import TimeTraps.Probability.KillingLifetimeTimeChange
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

/-! The actual positive clock maps the entire open time interval before
an extended lifetime onto the interval before its clock image. A global
real primitive supplies the Jacobian without differentiating the speed.
These sets and identities retain infinite lifetimes. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped NNReal Topology

noncomputable def positiveClockReal (v : PositiveTimeSpeed) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..s, v.rate r.toNNReal

def positiveTimeBefore (τ : WithTop ℝ) : Set ℝ := {s | 0 < s ∧ (s : WithTop ℝ) < τ}

theorem positiveTimeBefore_measurableSet (τ : WithTop ℝ) : MeasurableSet (positiveTimeBefore τ) := by
  cases τ with
  | top =>
    have he : positiveTimeBefore ⊤ = Ioi (0 : ℝ) := by ext s; simp [positiveTimeBefore]
    rw [he]
    exact measurableSet_Ioi
  | coe r =>
    have he : positiveTimeBefore (r : WithTop ℝ) = Ioo (0 : ℝ) r := by ext s; simp [positiveTimeBefore]
    rw [he]
    exact measurableSet_Ioo

theorem positiveClockReal_eq (v : PositiveTimeSpeed) {s : ℝ} (hs : 0 ≤ s) :
    positiveClockReal v s = (v.clock s.toNNReal : ℝ) := by
  exact congrArg (fun b : ℝ => ∫ r in (0 : ℝ)..b, v.rate r.toNNReal)
    (Real.coe_toNNReal s hs).symm

theorem positiveClockReal_hasDerivAt (v : PositiveTimeSpeed) (s : ℝ) :
    HasDerivAt (positiveClockReal v) (v.rate s.toNNReal) s := by
  have hc := v.continuous_rate.comp continuous_real_toNNReal
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem positiveClockReal_strictMonoOn (v : PositiveTimeSpeed) :
    StrictMonoOn (positiveClockReal v) (Ici (0 : ℝ)) := by
  intro s hs t ht hst
  rw [positiveClockReal_eq v hs, positiveClockReal_eq v ht]
  apply v.clock_strictMono
  change (s.toNNReal : ℝ) < (t.toNNReal : ℝ)
  rwa [Real.coe_toNNReal s hs, Real.coe_toNNReal t ht]

theorem positiveClockLifetimeMap_coe_lt_iff (e : ℝ≥0 ≃o ℝ≥0) (s : ℝ≥0) {τ : WithTop ℝ}
    (hτ : 0 ≤ τ) :
    ((e s : ℝ) : WithTop ℝ) < positiveClockLifetimeMap e τ ↔ (s.val : WithTop ℝ) < τ := by
  cases τ with
  | top => simp only [positiveClockLifetimeMap_top, WithTop.coe_lt_top]
  | coe r =>
    have hr : 0 ≤ r := WithTop.coe_le_coe.mp hτ
    simp only [positiveClockLifetimeMap_coe, WithTop.coe_lt_coe]
    have ho : e s < e r.toNNReal ↔ s < r.toNNReal := e.lt_iff_lt
    change (e s : ℝ) < (e r.toNNReal : ℝ) ↔ (s : ℝ) < (r.toNNReal : ℝ) at ho
    rwa [Real.coe_toNNReal r hr] at ho

theorem positiveClockReal_image_before (v : PositiveTimeSpeed) {τ : WithTop ℝ} (hτ : 0 ≤ τ) :
    positiveClockReal v '' positiveTimeBefore τ =
      positiveTimeBefore (positiveClockLifetimeMap v.clock τ) := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hsp : 0 < s.toNNReal := by
      change (0 : ℝ) < (s.toNNReal : ℝ)
      rw [Real.coe_toNNReal s hs.1.le]
      exact hs.1
    have hpos : 0 < positiveClockReal v s := by
      rw [positiveClockReal_eq v hs.1.le]
      have hp : v.clock 0 < v.clock s.toNNReal := v.clock_strictMono hsp
      rw [v.clock_zero] at hp
      exact hp
    refine ⟨hpos, ?_⟩
    rw [positiveClockReal_eq v hs.1.le]
    apply (positiveClockLifetimeMap_coe_lt_iff v.orderIso s.toNNReal hτ).mpr
    exact lt_of_eq_of_lt
      (congrArg (fun r : ℝ => (r : WithTop ℝ)) (Real.coe_toNNReal s hs.1.le)) hs.2
  · intro ht
    let s := v.inverse t.toNNReal
    have htp : 0 < t.toNNReal := by
      change (0 : ℝ) < (t.toNNReal : ℝ)
      rw [Real.coe_toNNReal t ht.1.le]
      exact ht.1
    have hsp : 0 < s := by
      simpa only [v.inverse_zero] using v.inverse_strictMono htp
    have hsclock : (v.clock s : ℝ) = t := by
      rw [v.clock_inverse]
      exact Real.coe_toNNReal t ht.1.le
    have hlt : (s.val : WithTop ℝ) < τ := by
      apply (positiveClockLifetimeMap_coe_lt_iff v.orderIso s hτ).mp
      change ((v.clock s : ℝ) : WithTop ℝ) < positiveClockLifetimeMap v.clock τ
      rw [hsclock]
      exact ht.2
    refine ⟨s.val, ⟨hsp, hlt⟩, ?_⟩
    exact hsclock

end TimeTraps.Probability
