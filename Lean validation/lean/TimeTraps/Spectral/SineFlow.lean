module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
Exact propagation of the value and derivative of a solution of u'' = -k²u.
The sinc form includes k=0 continuously. The propagation and reaction jump
are invertible, so a normalized nonzero solution never has value and slope
both zero. These are analytical formulas, not numerical shooting steps.
-/

namespace TimeTraps.Spectral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def sineValue (k a b x : ℝ) : ℝ :=
  a * Real.cos (k * x) + b * x * Real.sinc (k * x)

noncomputable def sineSlope (k a b x : ℝ) : ℝ :=
  -a * k * Real.sin (k * x) + b * Real.cos (k * x)

noncomputable def sineFlow (k x : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (sineValue k p.1 p.2 x, sineSlope k p.1 p.2 x)

def reactionJump (q : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.2 + q * p.1)

theorem scaled_sinc {k : ℝ} (hk : k ≠ 0) (x : ℝ) :
    x * Real.sinc (k * x) = Real.sin (k * x) / k := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hk hx)]
    field_simp

theorem sineValue_of_ne_zero {k : ℝ} (hk : k ≠ 0) (a b x : ℝ) :
    sineValue k a b x = a * Real.cos (k * x) + b / k * Real.sin (k * x) := by
  unfold sineValue
  rw [mul_assoc b, scaled_sinc hk]
  ring

theorem sineValue_zero_parameter (a b x : ℝ) : sineValue 0 a b x = a + b * x := by
  simp [sineValue]

theorem sineSlope_zero_parameter (a b x : ℝ) : sineSlope 0 a b x = b := by
  simp [sineSlope]

theorem sineFlow_zero (k : ℝ) (p : ℝ × ℝ) : sineFlow k 0 p = p := by
  cases p
  simp [sineFlow, sineValue, sineSlope]

theorem sineFlow_zero_parameter (x : ℝ) (p : ℝ × ℝ) :
    sineFlow 0 x p = (p.1 + p.2 * x, p.2) := by
  simp [sineFlow, sineValue_zero_parameter, sineSlope_zero_parameter]

theorem sineValue_continuous : Continuous (fun z : ℝ × ℝ × ℝ × ℝ =>
    sineValue z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold sineValue
  fun_prop

theorem sineSlope_continuous : Continuous (fun z : ℝ × ℝ × ℝ × ℝ =>
    sineSlope z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold sineSlope
  fun_prop

theorem sineValue_hasDerivAt (k a b x : ℝ) :
    HasDerivAt (sineValue k a b) (sineSlope k a b x) x := by
  by_cases hk : k = 0
  · subst k
    rw [show sineValue 0 a b = (fun t => a + b * t) from funext (sineValue_zero_parameter a b),
      sineSlope_zero_parameter]
    have hd := ((hasDerivAt_id x).const_mul b).const_add a
    change HasDerivAt (fun t : ℝ => a + b * t) (b * 1) x at hd
    rwa [mul_one] at hd
  · have he : sineValue k a b = fun t => a * Real.cos (k * t) + b / k * Real.sin (k * t) :=
      funext (sineValue_of_ne_zero hk a b)
    rw [he]
    have hd := (((hasDerivAt_id x).const_mul k).cos.const_mul a).add
      (((hasDerivAt_id x).const_mul k).sin.const_mul (b / k))
    have hc : a * (-Real.sin (k * x) * (k * 1)) + b / k * (Real.cos (k * x) * (k * 1)) =
        sineSlope k a b x := by
      unfold sineSlope
      field_simp
    change HasDerivAt (fun t => a * Real.cos (k * t) + b / k * Real.sin (k * t))
      (a * (-Real.sin (k * x) * (k * 1)) + b / k * (Real.cos (k * x) * (k * 1))) x at hd
    rwa [hc] at hd

theorem sineSlope_hasDerivAt (k a b x : ℝ) :
    HasDerivAt (sineSlope k a b) (-(k ^ 2) * sineValue k a b x) x := by
  by_cases hk : k = 0
  · subst k
    rw [show sineSlope 0 a b = (fun _ => b) from funext (sineSlope_zero_parameter a b)]
    simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_mul]
    exact hasDerivAt_const x b
  · have hd := (((hasDerivAt_id x).const_mul k).sin.const_mul (-a * k)).add
      (((hasDerivAt_id x).const_mul k).cos.const_mul b)
    have hc : (-a * k) * (Real.cos (k * x) * (k * 1)) + b * (-Real.sin (k * x) * (k * 1)) =
        -(k ^ 2) * sineValue k a b x := by
      rw [sineValue_of_ne_zero hk]
      field_simp
      ring
    change HasDerivAt (sineSlope k a b)
      ((-a * k) * (Real.cos (k * x) * (k * 1)) + b * (-Real.sin (k * x) * (k * 1))) x at hd
    rwa [hc] at hd

theorem sineFlow_inverse (k x : ℝ) (p : ℝ × ℝ) :
    sineFlow k (-x) (sineFlow k x p) = p := by
  by_cases hk : k = 0
  · subst k
    simp only [sineFlow_zero_parameter]
    apply Prod.ext
    · dsimp
      ring
    · rfl
  · apply Prod.ext
    · simp only [sineFlow, sineSlope, sineValue_of_ne_zero hk, mul_neg,
        Real.cos_neg, Real.sin_neg]
      calc
        _ = p.1 * (Real.sin (k * x) ^ 2 + Real.cos (k * x) ^ 2) := by
          field_simp
          ring
        _ = p.1 := by rw [Real.sin_sq_add_cos_sq, mul_one]
    · simp only [sineFlow, sineSlope, sineValue_of_ne_zero hk, mul_neg,
        Real.cos_neg, Real.sin_neg]
      calc
        _ = p.2 * (Real.sin (k * x) ^ 2 + Real.cos (k * x) ^ 2) := by
          field_simp
          ring
        _ = p.2 := by rw [Real.sin_sq_add_cos_sq, mul_one]

theorem sineFlow_ne_zero (k x : ℝ) {p : ℝ × ℝ} (hp : p ≠ (0, 0)) :
    sineFlow k x p ≠ (0, 0) := by
  intro h
  have hi := sineFlow_inverse k x p
  rw [h] at hi
  simp [sineFlow, sineValue, sineSlope] at hi
  exact hp hi.symm

theorem reactionJump_inverse (q : ℝ) (p : ℝ × ℝ) :
    reactionJump (-q) (reactionJump q p) = p := by
  cases p
  simp [reactionJump]

theorem reactionJump_ne_zero (q : ℝ) {p : ℝ × ℝ} (hp : p ≠ (0, 0)) :
    reactionJump q p ≠ (0, 0) := by
  intro h
  have hi := reactionJump_inverse q p
  rw [h] at hi
  simp [reactionJump] at hi
  exact hp hi.symm

end TimeTraps.Spectral
