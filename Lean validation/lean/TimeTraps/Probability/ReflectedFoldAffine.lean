module

public import TimeTraps.Probability.ReflectedFold

@[expose] public section

/-! Exact affine branches of the triangular fold, including a neighborhood
of every input whose folded value is strictly inside the interval. -/

namespace TimeTraps.Probability

open Set Filter
open scoped Topology

theorem reflectedFold_range (L : ℝ) (hL : 0 < L) : Set.range (reflectedFold L) = Icc 0 L := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact reflectedFold_mem L hL x
  · intro hy
    exact ⟨y, reflectedFold_eq_self L hL y hy⟩

theorem reflectedFold_round (L x : ℝ) :
    reflectedFold L x = |x - (round ((2 * L)⁻¹ * x) : ℝ) * (2 * L)| :=
  AddCircle.norm_eq (2 * L)

theorem reflectedFold_rising (L : ℝ) (hL : 0 < L) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc ((n : ℝ) * (2 * L)) ((n : ℝ) * (2 * L) + L)) :
    reflectedFold L x = x - (n : ℝ) * (2 * L) := by
  calc
    _ = reflectedFold L (x - (n : ℝ) * (2 * L)) :=
      ((reflectedFold_periodic L).sub_int_mul_eq n).symm
    _ = _ := reflectedFold_eq_self L hL _ ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem reflectedFold_falling (L : ℝ) (hL : 0 < L) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc ((n : ℝ) * (2 * L) - L) ((n : ℝ) * (2 * L))) :
    reflectedFold L x = (n : ℝ) * (2 * L) - x := by
  calc
    _ = reflectedFold L ((n : ℝ) * (2 * L) - x) :=
      ((reflectedFold_periodic L).int_mul_sub_eq n |>.trans (reflectedFold_neg L x)).symm
    _ = _ := reflectedFold_eq_self L hL _ ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem reflectedFold_locally_rising (L : ℝ) (hL : 0 < L) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo ((n : ℝ) * (2 * L)) ((n : ℝ) * (2 * L) + L)) :
    ∀ᶠ y in 𝓝 x, reflectedFold L y = reflectedFold L x + (y - x) := by
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  rw [reflectedFold_rising L hL n x ⟨hx.1.le, hx.2.le⟩,
    reflectedFold_rising L hL n y ⟨hy.1.le, hy.2.le⟩]
  ring

theorem reflectedFold_locally_falling (L : ℝ) (hL : 0 < L) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo ((n : ℝ) * (2 * L) - L) ((n : ℝ) * (2 * L))) :
    ∀ᶠ y in 𝓝 x, reflectedFold L y = reflectedFold L x - (y - x) := by
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  rw [reflectedFold_falling L hL n x ⟨hx.1.le, hx.2.le⟩,
    reflectedFold_falling L hL n y ⟨hy.1.le, hy.2.le⟩]
  ring

theorem reflectedFold_local_affine (L : ℝ) (hL : 0 < L) (x : ℝ)
    (hx : reflectedFold L x ∈ Ioo 0 L) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ᶠ y in 𝓝 x, reflectedFold L y = reflectedFold L x + σ * (y - x) := by
  let n : ℤ := round ((2 * L)⁻¹ * x)
  have heq : reflectedFold L x = |x - (n : ℝ) * (2 * L)| := reflectedFold_round L x
  by_cases hr : 0 ≤ x - (n : ℝ) * (2 * L)
  · rw [abs_of_nonneg hr] at heq
    have hi : x ∈ Ioo ((n : ℝ) * (2 * L)) ((n : ℝ) * (2 * L) + L) :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    refine ⟨1, Or.inl rfl, ?_⟩
    simpa only [one_mul] using reflectedFold_locally_rising L hL n x hi
  · rw [abs_of_neg (lt_of_not_ge hr)] at heq
    have hi : x ∈ Ioo ((n : ℝ) * (2 * L) - L) ((n : ℝ) * (2 * L)) :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    refine ⟨-1, Or.inr rfl, ?_⟩
    simpa only [neg_one_mul, sub_eq_add_neg] using reflectedFold_locally_falling L hL n x hi

end TimeTraps.Probability
