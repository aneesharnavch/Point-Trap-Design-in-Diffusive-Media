module

public import TimeTraps.Analysis.ReflectedFoldTanakaGeometry

@[expose] public section

/-! Away from the corner lattice, the actual periodic fold slope is
locally constant with value +1 or -1. In particular it is continuous there
and its square is one. No assertion of continuity at a corner is made. -/

namespace TimeTraps.Analysis

open Set Filter TimeTraps.Probability
open scoped Topology

theorem reflectedFold_interior_of_ne_lattice (L : ℝ) (hL : 0 < L) (z : ℝ)
    (hz : ∀ j : ℤ, z ≠ j * L) : reflectedFold L z ∈ Ioo 0 L := by
  let r := reflectedFold L z
  have hr : r ∈ Icc 0 L := reflectedFold_mem L hL z
  obtain ⟨k, hk | hk⟩ := (reflectedFold_eq_iff_lattice L hL z r hr).mp rfl
  all_goals
    have h0 : r ≠ 0 := by
      intro he
      rw [he] at hk
      apply hz (2 * k)
      push_cast
      linarith
    have h1 : r ≠ L := by
      intro he
      rw [he] at hk
      first
      | apply hz (2 * k + 1); push_cast; linarith
      | apply hz (2 * k - 1); push_cast; linarith
    exact ⟨lt_of_le_of_ne hr.1 (Ne.symm h0), lt_of_le_of_ne hr.2 h1⟩

theorem reflectedFoldSlope_locally_signed (L : ℝ) (hL : 0 < L) (z : ℝ)
    (hz : ∀ j : ℤ, z ≠ j * L) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ reflectedFoldSlope L z = c ∧
      ∀ᶠ w in 𝓝 z, reflectedFoldSlope L w = c := by
  let r := reflectedFold L z
  have hr : r ∈ Ioo 0 L := reflectedFold_interior_of_ne_lattice L hL z hz
  obtain ⟨k, hk | hk⟩ := (reflectedFold_eq_iff_lattice L hL z r ⟨hr.1.le, hr.2.le⟩).mp rfl
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · rw [hk]
      exact reflectedFoldSlope_rising L hL k r hr
    · have hi : z ∈ Ioo ((k : ℝ) * (2 * L)) ((k : ℝ) * (2 * L) + L) := by
        constructor <;> linarith [hr.1, hr.2]
      filter_upwards [Ioo_mem_nhds hi.1 hi.2] with w hw
      have hh := reflectedFoldSlope_rising L hL k (w - (k : ℝ) * (2 * L))
        ⟨by linarith [hw.1], by linarith [hw.2]⟩
      rwa [sub_add_cancel] at hh
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · rw [hk]
      exact reflectedFoldSlope_falling L hL k r hr
    · have hi : z ∈ Ioo ((k : ℝ) * (2 * L) - L) ((k : ℝ) * (2 * L)) := by
        constructor <;> linarith [hr.1, hr.2]
      filter_upwards [Ioo_mem_nhds hi.1 hi.2] with w hw
      have hh := reflectedFoldSlope_falling L hL k ((k : ℝ) * (2 * L) - w)
        ⟨by linarith [hw.2], by linarith [hw.1]⟩
      convert hh using 1
      congr 1
      ring

theorem reflectedFoldSlope_square_eq_one (L : ℝ) (hL : 0 < L) (z : ℝ)
    (hz : ∀ j : ℤ, z ≠ j * L) : reflectedFoldSlope L z ^ 2 = 1 := by
  obtain ⟨c, hc, he, _⟩ := reflectedFoldSlope_locally_signed L hL z hz
  rcases hc with rfl | rfl <;> rw [he] <;> norm_num

theorem reflectedFoldSlope_locally_constant (L : ℝ) (hL : 0 < L) (z : ℝ)
    (hz : ∀ j : ℤ, z ≠ j * L) :
    ∀ᶠ w in 𝓝 z, reflectedFoldSlope L w = reflectedFoldSlope L z := by
  obtain ⟨c, _, he, hh⟩ := reflectedFoldSlope_locally_signed L hL z hz
  exact hh.mono (fun _ hw => hw.trans he.symm)

theorem reflectedFoldSlope_continuousAt (L : ℝ) (hL : 0 < L) (z : ℝ)
    (hz : ∀ j : ℤ, z ≠ j * L) : ContinuousAt (reflectedFoldSlope L) z := by
  have he : reflectedFoldSlope L =ᶠ[𝓝 z] (fun _ => reflectedFoldSlope L z) :=
    reflectedFoldSlope_locally_constant L hL z hz
  exact continuousAt_const.congr_of_eventuallyEq he

end TimeTraps.Analysis
