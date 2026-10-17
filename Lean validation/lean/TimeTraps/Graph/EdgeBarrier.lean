module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
Sharp quadratic edge barriers, including exterior quadratic vertices and
both equality conditions. `q` is the curvature ρ/a. The cost is the integral
of ρ(M-u)+a(u')² after writing M-u=d+q(x-z)²/2; its algebraic identification
with that physical integrand is proved below.
-/

namespace TimeTraps.Graph

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def edgeCost (ρ q d z L : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, ρ * (d + 3 * q / 2 * (x - z) ^ 2)

theorem edge_integrand_identity (ρ a d z x : ℝ) (ha : a ≠ 0) :
    ρ * (d + (ρ / a) / 2 * (x - z) ^ 2) + a * ((ρ / a) * (x - z)) ^ 2 =
      ρ * (d + 3 * (ρ / a) / 2 * (x - z) ^ 2) := by
  field_simp
  ring

/-- The exact integral, with no positivity assumptions. -/
theorem edgeCost_eq (ρ q d z L : ℝ) :
    edgeCost ρ q d z L = ρ * q * L ^ 3 / 8 +
      ρ * L * (d + 3 * q / 2 * (z - L / 2) ^ 2) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => ρ * d * y + ρ * q / 2 * (y - z) ^ 3)
        (ρ * (d + 3 * q / 2 * (x - z) ^ 2)) x := by
    intro x
    convert! ((hasDerivAt_id x).const_mul (ρ * d)).add
      ((((hasDerivAt_id x).sub_const z).pow 3).const_mul (ρ * q / 2)) using 1
    simp
    ring
  have hint : IntervalIntegrable
      (fun x : ℝ => ρ * (d + 3 * q / 2 * (x - z) ^ 2)) MeasureTheory.volume 0 L :=
    (continuous_const.mul (continuous_const.add
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)))).intervalIntegrable _ _
  unfold edgeCost
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint]
  ring

/-- The excess over the ordinary-edge barrier is nonnegative, and vanishes
exactly for the centered quadratic touching zero. -/
theorem quadratic_excess_nonneg_eq_iff {q d z L : ℝ} (hq : 0 < q) (hL : 0 < L)
    (hw : ∀ x ∈ Set.Icc (0 : ℝ) L, 0 ≤ d + q / 2 * (x - z) ^ 2) :
    0 ≤ d + 3 * q / 2 * (z - L / 2) ^ 2 ∧
      (d + 3 * q / 2 * (z - L / 2) ^ 2 = 0 ↔ d = 0 ∧ z = L / 2) := by
  have hcoef : 0 < 3 * q / 2 := by positivity
  have hsq : 0 ≤ 3 * q / 2 * (z - L / 2) ^ 2 :=
    mul_nonneg hcoef.le (sq_nonneg _)
  by_cases hz0 : 0 ≤ z
  · by_cases hzL : z ≤ L
    · have hd := hw z ⟨hz0, hzL⟩
      simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hd
      refine ⟨add_nonneg hd hsq, ?_⟩
      constructor
      · intro heq
        have hd0 : d = 0 := by linarith
        have hprod : 3 * q / 2 * (z - L / 2) ^ 2 = 0 := by linarith
        have hz : (z - L / 2) ^ 2 = 0 :=
          (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hcoef)
        exact ⟨hd0, sub_eq_zero.mp ((sq_eq_zero_iff.mp hz))⟩
      · rintro ⟨rfl, rfl⟩
        ring
    · have hz : L < z := lt_of_not_ge hzL
      have hend := hw L ⟨hL.le, le_rfl⟩
      have h₁ := mul_nonneg hq.le (sq_nonneg (z - L))
      have h₂ := mul_nonneg (mul_nonneg hq.le (sub_nonneg.mpr hz.le)) hL.le
      have h₃ := mul_pos hq (sq_pos_of_pos hL)
      have hstrict : 0 < d + 3 * q / 2 * (z - L / 2) ^ 2 := by nlinarith
      refine ⟨hstrict.le, ?_⟩
      constructor
      · intro hzero
        linarith
      · rintro ⟨_, heq⟩
        linarith
  · have hz : z < 0 := lt_of_not_ge hz0
    have hend := hw 0 ⟨le_rfl, hL.le⟩
    have h₁ := mul_nonneg hq.le (sq_nonneg z)
    have h₂ := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hq.le hz.le) hL.le
    have h₃ := mul_pos hq (sq_pos_of_pos hL)
    have hstrict : 0 < d + 3 * q / 2 * (z - L / 2) ^ 2 := by nlinarith
    refine ⟨hstrict.le, ?_⟩
    constructor
    · intro hzero
      linarith
    · rintro ⟨_, heq⟩
      linarith

/-- Ordinary-edge barrier with its complete equality characterization. -/
theorem ordinary_edge_barrier {ρ q d z L : ℝ}
    (hρ : 0 < ρ) (hq : 0 < q) (hL : 0 < L)
    (hw : ∀ x ∈ Set.Icc (0 : ℝ) L, 0 ≤ d + q / 2 * (x - z) ^ 2) :
    ρ * q * L ^ 3 / 8 ≤ edgeCost ρ q d z L ∧
      (edgeCost ρ q d z L = ρ * q * L ^ 3 / 8 ↔ d = 0 ∧ z = L / 2) := by
  obtain ⟨hnonneg, heq⟩ := quadratic_excess_nonneg_eq_iff hq hL hw
  have hρL := mul_pos hρ hL
  rw [edgeCost_eq]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg hρL.le hnonneg)
  · constructor
    · intro h
      apply heq.mp
      have : ρ * L * (d + 3 * q / 2 * (z - L / 2) ^ 2) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hρL)
    · intro h
      rw [heq.mpr h, mul_zero, add_zero]

/-- A reflecting tip places the quadratic vertex at L and gives factor four. -/
theorem reflecting_edge_barrier {ρ q d L : ℝ}
    (hρ : 0 < ρ) (hL : 0 < L) (hd : 0 ≤ d) :
    ρ * q * L ^ 3 / 2 ≤ edgeCost ρ q d L L ∧
      (edgeCost ρ q d L L = ρ * q * L ^ 3 / 2 ↔ d = 0) := by
  have hid : edgeCost ρ q d L L = ρ * q * L ^ 3 / 2 + ρ * L * d := by
    rw [edgeCost_eq]
    ring
  rw [hid]
  have hρL := mul_pos hρ hL
  refine ⟨le_add_of_nonneg_right (mul_nonneg hρL.le hd), ?_⟩
  constructor
  · intro h
    have : ρ * L * d = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hρL)
  · rintro rfl
    ring

end TimeTraps.Graph
