module

public import TimeTraps.Analysis.IntervalEnergy
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public section

/-!
Restriction and translation of the independent interval energy space, and
an energy-membership criterion from an integrable derivative outside a
countable exceptional set. These apply to arbitrary energy test functions.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory

theorem IntervalEnergy.mono {u : ℝ → ℝ} {l r a b : ℝ} (hu : IntervalEnergy u l r)
    (hab : uIcc a b ⊆ uIcc l r) : IntervalEnergy u a b :=
  ⟨hu.absolutelyContinuous.mono hab, hu.derivative_square_integrable.mono_set hab⟩

theorem IntervalEnergy.congr {u v : ℝ → ℝ} {l r : ℝ} (hu : IntervalEnergy u l r)
    (heq : EqOn u v (uIcc l r)) : IntervalEnergy v l r := by
  refine ⟨interval_absolutelyContinuous_congr hu.absolutelyContinuous heq, ?_⟩
  apply hu.derivative_square_integrable.congr_uIoo
  intro x hx
  change deriv u x ^ 2 = deriv v x ^ 2
  rw [((heq.mono Ioo_subset_Icc_self).deriv isOpen_Ioo) hx]

theorem interval_absolutelyContinuous_translate {u : ℝ → ℝ} {l r : ℝ}
    (hu : AbsolutelyContinuousOnInterval u l r) (hlr : l ≤ r) (t : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => u (t + x)) (l - t) (r - t) := by
  have hi := hu.intervalIntegrable_deriv.comp_add_left t
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : l - t ∈ uIcc (l - t) (r - t))
  have hac := (interval_absolutelyContinuous_const (u l) (l - t) (r - t)).fun_add hp
  apply interval_absolutelyContinuous_congr hac
  intro x hx
  have hx' : x ∈ Icc (l - t) (r - t) := by
    simpa only [uIcc_of_le (sub_le_sub_right hlr t)] using hx
  have hy : t + x ∈ Icc l r := ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hs : AbsolutelyContinuousOnInterval u l (t + x) := hu.mono (by
    rw [uIcc_of_le hy.1, uIcc_of_le hlr]
    exact Icc_subset_Icc le_rfl hy.2)
  change u l + (∫ s in (l - t)..x, deriv u (t + s)) = u (t + x)
  rw [intervalIntegral.integral_comp_add_left, add_sub_cancel, hs.integral_deriv_eq_sub]
  ring

theorem IntervalEnergy.translate {u : ℝ → ℝ} {l r : ℝ} (hu : IntervalEnergy u l r)
    (hlr : l ≤ r) (t : ℝ) : IntervalEnergy (fun x => u (t + x)) (l - t) (r - t) := by
  refine ⟨interval_absolutelyContinuous_translate hu.absolutelyContinuous hlr t, ?_⟩
  simpa only [deriv_comp_const_add] using hu.derivative_square_integrable.comp_add_left t

/-- A continuous function on a closed finite interval, extended by zero off
the open interval, is square integrable on the whole real line. -/
theorem continuousOn_indicator_memLp_two {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b)) : MemLp ((Ioo a b).indicator g) 2 volume := by
  have hi : Integrable ((Ioo a b).indicator g) volume :=
    (hg.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr
  have he : (fun x => ((Ioo a b).indicator g x) ^ 2) =
      (Ioo a b).indicator (fun x => g x ^ 2) := by
    funext x
    by_cases hx : x ∈ Ioo a b <;> simp [hx]
  rw [he]
  exact ((hg.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo

/-- The derivative hypothesis is required only off a countable set. Both
absolute continuity and square integrability of the actual derivative follow. -/
theorem intervalEnergy_of_derivative_off_countable {u g : ℝ → ℝ} {l r : ℝ} {s : Set ℝ}
    (hlr : l ≤ r) (hs : s.Countable) (hu : ContinuousOn u (Icc l r))
    (hd : ∀ x ∈ Ioo l r \ s, HasDerivAt u (g x) x)
    (hg : IntervalIntegrable g volume l r)
    (hg₂ : IntervalIntegrable (fun x => g x ^ 2) volume l r) : IntervalEnergy u l r := by
  have hp := hg.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : l ∈ uIcc l r)
  have hac := (interval_absolutelyContinuous_const (u l) l r).fun_add hp
  constructor
  · apply interval_absolutelyContinuous_congr hac
    intro x hx
    have hx' : x ∈ Icc l r := by simpa only [uIcc_of_le hlr] using hx
    have hi : IntervalIntegrable g volume l x := hg.mono_set (by
      rw [uIcc_of_le hx'.1, uIcc_of_le hlr]
      exact Icc_subset_Icc le_rfl hx'.2)
    have he := integral_eq_of_hasDerivAt_off_countable_of_le u g hx'.1 hs
      (hu.mono (Icc_subset_Icc le_rfl hx'.2))
      (fun y hy => hd y ⟨⟨hy.1.1, hy.1.2.trans_le hx'.2⟩, hy.2⟩) hi
    change u l + (∫ t in l..x, g t) = u x
    linarith
  · apply hg₂.congr_ae
    rw [uIoc_of_le hlr]
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hs.ae_notMem volume, volume.ae_ne r] with x hxs hxr hx
    have hxi : x ∈ Ioo l r := ⟨hx.1, lt_of_le_of_ne hx.2 hxr⟩
    rw [(hd x ⟨hxi, hxs⟩).deriv]

end TimeTraps.Analysis
