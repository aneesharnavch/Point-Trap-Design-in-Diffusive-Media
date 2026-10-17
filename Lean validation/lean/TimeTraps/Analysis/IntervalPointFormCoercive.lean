module

public import TimeTraps.Analysis.IntervalPointForm

@[expose] public section

/-! Coercivity on every nondegenerate finite interval, with the physical
length retained in both constants. One strictly positive contact suffices. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

theorem intervalPointForm_coercivity_constant_pos {D κ l r : ℝ}
    (hD : 0 < D) (hκ : 0 < κ) (hlr : l < r) :
    0 < min (D / (2 * (r - l) ^ 2 + 1)) (κ / (2 * (r - l))) :=
  lt_min (div_pos hD (by positivity)) (div_pos hκ (mul_pos (by norm_num) (sub_pos.mpr hlr)))

theorem IntervalEnergy.interval_point_form_coercive {ι : Type*} [Fintype ι]
    {D l r : ℝ} {κ z : ι → ℝ} (hD : 0 ≤ D) (hlr : l < r) (hκ : ∀ i, 0 ≤ κ i)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (k : ι) (hz : z k ∈ Icc l r) :
    min (D / (2 * (r - l) ^ 2 + 1)) (κ k / (2 * (r - l))) * intervalH1SizeSq u l r ≤
      intervalPointForm D κ z l r u u := by
  let A := 2 * (r - l) ^ 2 + 1
  let B := 2 * (r - l)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 < B := mul_pos (by norm_num) (sub_pos.mpr hlr)
  let c := min (D / A) (κ k / B)
  have hc : 0 ≤ c := le_min (div_nonneg hD hA.le) (div_nonneg (hκ k) hB.le)
  have hcA : c * A ≤ D := (le_div_iff₀ hA).mp (min_le_left _ _)
  have hcB : c * B ≤ κ k := (le_div_iff₀ hB).mp (min_le_right _ _)
  have hE : 0 ≤ ∫ x in l..r, deriv u x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hlr.le (fun x => sq_nonneg (deriv u x))
  change c * intervalH1SizeSq u l r ≤ _
  calc
    _ ≤ c * (B * u (z k) ^ 2 + A * (∫ x in l..r, deriv u x ^ 2)) :=
      mul_le_mul_of_nonneg_left (hu.h1_control hz) hc
    _ = (c * B) * u (z k) ^ 2 + (c * A) * (∫ x in l..r, deriv u x ^ 2) := by ring
    _ ≤ κ k * u (z k) ^ 2 + D * (∫ x in l..r, deriv u x ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right hcB (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hcA hE)
    _ ≤ intervalPointForm D κ z l r u u := by
      simpa only [add_comm] using intervalPointForm_lower_single D κ z l r hκ u k

end TimeTraps.Analysis
