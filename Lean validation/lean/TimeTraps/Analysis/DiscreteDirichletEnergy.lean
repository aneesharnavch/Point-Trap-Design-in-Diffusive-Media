module

public import TimeTraps.Analysis.FinitePrefix
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Finite Dirichlet energy and the positive-ground-state comparison. Endpoint
values are retained as actual entries and are assumed to vanish. -/

namespace TimeTraps.Analysis

open scoped BigOperators

theorem discrete_weighted_two_product (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haz : a = 0 → u = 0) (hbz : b = 0 → v = 0) :
    2 * u * v ≤ b / a * u ^ 2 + a / b * v ^ 2 := by
  by_cases ha0 : a = 0
  · simp [ha0, haz ha0]
  by_cases hb0 : b = 0
  · simp [hb0, hbz hb0]
  have hab : 0 < a * b := mul_pos (lt_of_le_of_ne ha (Ne.symm ha0))
    (lt_of_le_of_ne hb (Ne.symm hb0))
  apply (mul_le_mul_iff_right₀ hab).mp
  have hid : (b / a * u ^ 2 + a / b * v ^ 2 - 2 * u * v) * (a * b) =
      (b * u - a * v) ^ 2 := by
    field_simp
    ring
  nlinarith [sq_nonneg (b * u - a * v)]

theorem discrete_dirichlet_sum_interior {n : ℕ} (s : Fin (n + 2) → ℝ)
    (h0 : s 0 = 0) (hlast : s (Fin.last (n + 1)) = 0) :
    (∑ i, s i ^ 2) = ∑ i : Fin n, s i.succ.castSucc ^ 2 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp [h0, hlast]

theorem discrete_dirichlet_energy_expansion {n : ℕ} (s : Fin (n + 1) → ℝ)
    (h0 : s 0 = 0) (hlast : s (Fin.last n) = 0) :
    (∑ i : Fin n, (s i.succ - s i.castSucc) ^ 2) =
      2 * (∑ i, s i ^ 2) - 2 * ∑ i : Fin n, s i.castSucc * s i.succ := by
  have hl : (∑ i : Fin n, s i.castSucc ^ 2) = ∑ i, s i ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    simp [hlast]
  have hr : (∑ i : Fin n, s i.succ ^ 2) = ∑ i, s i ^ 2 := by
    rw [Fin.sum_univ_succ]
    simp [h0]
  calc
    _ = ∑ i : Fin n, (s i.succ ^ 2 + s i.castSucc ^ 2 -
        2 * (s i.castSucc * s i.succ)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hl, hr]
      ring

theorem discrete_dirichlet_weighted_sum {n : ℕ} (s g : Fin (n + 2) → ℝ)
    (c : ℝ) (h0 : s 0 = 0) (hlast : s (Fin.last (n + 1)) = 0)
    (hg : ∀ i : Fin n, 0 < g i.succ.castSucc)
    (heig : ∀ i : Fin n, g i.castSucc.castSucc + g i.succ.succ =
      c * g i.succ.castSucc) :
    (∑ i : Fin (n + 1), (g i.succ / g i.castSucc * s i.castSucc ^ 2 +
      g i.castSucc / g i.succ * s i.succ ^ 2)) = c * ∑ i, s i ^ 2 := by
  rw [discrete_dirichlet_sum_interior s h0 hlast]
  rw [Finset.sum_add_distrib,
    Fin.sum_univ_succ (fun i : Fin (n + 1) => g i.succ / g i.castSucc * s i.castSucc ^ 2),
    Fin.sum_univ_castSucc (fun i : Fin (n + 1) => g i.castSucc / g i.succ * s i.succ ^ 2)]
  simp only [Fin.castSucc_zero, Fin.succ_last, h0, hlast, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_add, add_zero, Fin.castSucc_succ]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := heig i
  have hne := ne_of_gt (hg i)
  simp only [Fin.castSucc_succ] at hi hne
  rw [← add_mul, ← add_div]
  rw [add_comm, hi, mul_div_cancel_right₀ _ hne]

theorem discrete_dirichlet_ground_bound {n : ℕ} (s g : Fin (n + 2) → ℝ)
    (c : ℝ) (h0 : s 0 = 0) (hlast : s (Fin.last (n + 1)) = 0)
    (hg : ∀ i, 0 ≤ g i) (hgz : ∀ i, g i = 0 → s i = 0)
    (hpos : ∀ i : Fin n, 0 < g i.succ.castSucc)
    (heig : ∀ i : Fin n, g i.castSucc.castSucc + g i.succ.succ =
      c * g i.succ.castSucc) :
    (2 - c) * (∑ i, s i ^ 2) ≤
      ∑ i : Fin (n + 1), (s i.succ - s i.castSucc) ^ 2 := by
  have hb := Finset.sum_le_sum (fun (i : Fin (n + 1)) (_ : i ∈ Finset.univ) =>
    discrete_weighted_two_product (g i.castSucc) (g i.succ) (s i.castSucc) (s i.succ)
      (hg _) (hg _) (hgz _) (hgz _))
  rw [discrete_dirichlet_weighted_sum s g c h0 hlast hpos heig] at hb
  have hs : (∑ i : Fin (n + 1), 2 * s i.castSucc * s i.succ) =
      2 * ∑ i : Fin (n + 1), s i.castSucc * s i.succ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs] at hb
  rw [discrete_dirichlet_energy_expansion s h0 hlast]
  nlinarith

theorem discrete_div_mul_square (a b : ℝ) : a / b * b ^ 2 = a * b := by
  by_cases hb : b = 0
  · simp [hb]
  · field_simp

theorem discrete_dirichlet_ground_energy {n : ℕ} (g : Fin (n + 2) → ℝ)
    (c : ℝ) (h0 : g 0 = 0) (hlast : g (Fin.last (n + 1)) = 0)
    (hpos : ∀ i : Fin n, 0 < g i.succ.castSucc)
    (heig : ∀ i : Fin n, g i.castSucc.castSucc + g i.succ.succ =
      c * g i.succ.castSucc) :
    (∑ i : Fin (n + 1), (g i.succ - g i.castSucc) ^ 2) =
      (2 - c) * ∑ i, g i ^ 2 := by
  have hw := discrete_dirichlet_weighted_sum g g c h0 hlast hpos heig
  simp_rw [discrete_div_mul_square] at hw
  have hs : (∑ i : Fin (n + 1),
      (g i.succ * g i.castSucc + g i.castSucc * g i.succ)) =
      2 * ∑ i : Fin (n + 1), g i.castSucc * g i.succ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs] at hw
  rw [discrete_dirichlet_energy_expansion g h0 hlast]
  nlinarith

end TimeTraps.Analysis
