module

public import TimeTraps.Analysis.IntervalEnergy
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! Positive exact sine interpolation between prescribed endpoint values. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis

noncomputable def sineInterpolation (k l a b x : ℝ) : ℝ :=
  (a * Real.sin (k * (l - x)) + b * Real.sin (k * x)) / Real.sin (k * l)

noncomputable def sineInterpolationSlope (k l a b x : ℝ) : ℝ :=
  k * (b * Real.cos (k * x) - a * Real.cos (k * (l - x))) / Real.sin (k * l)

theorem sineInterpolation_hasDerivAt (k l a b x : ℝ) :
    HasDerivAt (sineInterpolation k l a b) (sineInterpolationSlope k l a b x) x := by
  have h := ((((hasDerivAt_const x l).sub (hasDerivAt_id x)).const_mul k).sin.const_mul a).add
    (((hasDerivAt_id x).const_mul k).sin.const_mul b)
  have hd := h.div_const (Real.sin (k * l))
  convert hd using 1 <;> first | rfl |
    (dsimp only [sineInterpolationSlope, Pi.sub_apply, id_eq]; ring)

theorem sineInterpolationSlope_hasDerivAt (k l a b x : ℝ) :
    HasDerivAt (sineInterpolationSlope k l a b) (-k ^ 2 * sineInterpolation k l a b x) x := by
  have h := (((hasDerivAt_id x).const_mul k).cos.const_mul b).sub
    ((((hasDerivAt_const x l).sub (hasDerivAt_id x)).const_mul k).cos.const_mul a)
  have hd := (h.const_mul k).div_const (Real.sin (k * l))
  convert hd using 1 <;> first | rfl |
    (dsimp only [sineInterpolation, Pi.sub_apply, id_eq]; ring)

theorem sineInterpolation_continuous (k l a b : ℝ) : Continuous (sineInterpolation k l a b) :=
  continuous_iff_continuousAt.mpr fun x => (sineInterpolation_hasDerivAt k l a b x).continuousAt

theorem sineInterpolationSlope_continuous (k l a b : ℝ) :
    Continuous (sineInterpolationSlope k l a b) :=
  continuous_iff_continuousAt.mpr fun x => (sineInterpolationSlope_hasDerivAt k l a b x).continuousAt

theorem sineInterpolation_energy {l : ℝ} (hl : 0 ≤ l) (k a b : ℝ) :
    IntervalEnergy (sineInterpolation k l a b) 0 l :=
  intervalEnergy_of_continuous_derivative hl (sineInterpolation_continuous k l a b).continuousOn
    (sineInterpolationSlope_continuous k l a b).continuousOn
    (fun x _ => sineInterpolation_hasDerivAt k l a b x)

theorem sineInterpolation_left {k l : ℝ} (hs : Real.sin (k * l) ≠ 0) (a b : ℝ) :
    sineInterpolation k l a b 0 = a := by
  simp [sineInterpolation, hs]

theorem sineInterpolation_right {k l : ℝ} (hs : Real.sin (k * l) ≠ 0) (a b : ℝ) :
    sineInterpolation k l a b l = b := by
  simp [sineInterpolation, hs]

theorem sineInterpolationSlope_left (k l a b : ℝ) :
    sineInterpolationSlope k l a b 0 = k * (b - a * Real.cos (k * l)) / Real.sin (k * l) := by
  simp [sineInterpolationSlope]

theorem sineInterpolationSlope_right (k l a b : ℝ) :
    sineInterpolationSlope k l a b l = k * (b * Real.cos (k * l) - a) / Real.sin (k * l) := by
  simp [sineInterpolationSlope]

theorem sineInterpolation_pos {k l a b : ℝ} (hk : 0 < k) (hl : 0 < l)
    (hp : k * l < Real.pi) (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : x ∈ Icc 0 l) :
    0 < sineInterpolation k l a b x := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (mul_pos hk hl) hp
  by_cases hz : x = 0
  · rw [hz, sineInterpolation_left (ne_of_gt hs)]
    exact ha
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hz)
  have hxr : k * x < Real.pi :=
    (mul_le_mul_of_nonneg_left hx.2 hk.le).trans_lt hp
  have hxs := Real.sin_pos_of_pos_of_lt_pi (mul_pos hk hxpos) hxr
  have hls : 0 ≤ Real.sin (k * (l - x)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hk.le (sub_nonneg.mpr hx.2))
      ((mul_le_mul_of_nonneg_left (sub_le_self l hx.1) hk.le).trans hp.le)
  exact div_pos (add_pos_of_nonneg_of_pos (mul_nonneg ha.le hls) (mul_pos hb hxs)) hs

end TimeTraps.Spectral
