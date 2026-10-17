module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Deterministic finite quadratic-variation algebra. A monotone path is
controlled by its largest increment times its total increment. Vanishing
quadratic variation is stable under subtraction and does not affect the
quadratic-variation limit of another path. -/

namespace TimeTraps.Analysis

open Filter
open scoped Topology

def finiteQuadraticVariation {N : ℕ} (v : Fin (N + 1) → ℝ) : ℝ :=
  ∑ i : Fin N, (v i.succ - v i.castSucc) ^ 2

theorem finiteQuadraticVariation_nonneg {N : ℕ} (v : Fin (N + 1) → ℝ) :
    0 ≤ finiteQuadraticVariation v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem finite_sum_increments {N : ℕ} (v : Fin (N + 1) → ℝ) :
    (∑ i : Fin N, (v i.succ - v i.castSucc)) = v (Fin.last N) - v 0 := by
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_succ v
  have h₂ := Fin.sum_univ_castSucc v
  linarith

theorem finiteQuadraticVariation_monotone_bound {N : ℕ} (v : Fin (N + 1) → ℝ)
    (hv : Monotone v) {ε : ℝ} (he : ∀ i : Fin N, v i.succ - v i.castSucc ≤ ε) :
    finiteQuadraticVariation v ≤ ε * (v (Fin.last N) - v 0) := by
  calc
    _ ≤ ∑ i : Fin N, ε * (v i.succ - v i.castSucc) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : 0 ≤ v i.succ - v i.castSucc := sub_nonneg.mpr (hv (Fin.castSucc_le_succ i))
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (he i) hi
    _ = _ := by rw [← Finset.mul_sum, finite_sum_increments]

theorem finiteQuadraticVariation_sub_le {N : ℕ} (v w : Fin (N + 1) → ℝ) :
    finiteQuadraticVariation (fun i => v i - w i) ≤
      2 * finiteQuadraticVariation v + 2 * finiteQuadraticVariation w := by
  unfold finiteQuadraticVariation
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg ((v i.succ - v i.castSucc) + (w i.succ - w i.castSucc))]

theorem finiteQuadraticVariation_affine {N : ℕ} (v : Fin (N + 1) → ℝ) (a c : ℝ) :
    finiteQuadraticVariation (fun i => c + a * v i) = a ^ 2 * finiteQuadraticVariation v := by
  unfold finiteQuadraticVariation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finiteQuadraticVariation_sub_tendsto_zero (N : ℕ → ℕ)
    (v w : (n : ℕ) → Fin (N n + 1) → ℝ)
    (hv : Tendsto (fun n => finiteQuadraticVariation (v n)) atTop (𝓝 0))
    (hw : Tendsto (fun n => finiteQuadraticVariation (w n)) atTop (𝓝 0)) :
    Tendsto (fun n => finiteQuadraticVariation (fun i => v n i - w n i)) atTop (𝓝 0) := by
  have hb := (hv.const_mul 2).add (hw.const_mul 2)
  simp only [mul_zero, add_zero] at hb
  exact squeeze_zero (fun n => finiteQuadraticVariation_nonneg _)
    (fun n => finiteQuadraticVariation_sub_le (v n) (w n)) hb

theorem finiteQuadraticVariation_add_tendsto (N : ℕ → ℕ)
    (v w : (n : ℕ) → Fin (N n + 1) → ℝ) (A : ℝ)
    (hv : Tendsto (fun n => finiteQuadraticVariation (v n)) atTop (𝓝 A))
    (hw : Tendsto (fun n => finiteQuadraticVariation (w n)) atTop (𝓝 0)) :
    Tendsto (fun n => finiteQuadraticVariation (fun i => v n i + w n i)) atTop (𝓝 A) := by
  let C (n : ℕ) : ℝ := ∑ i : Fin (N n),
    (v n i.succ - v n i.castSucc) * (w n i.succ - w n i.castSucc)
  have hb (n : ℕ) : C n ^ 2 ≤ finiteQuadraticVariation (v n) * finiteQuadraticVariation (w n) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hp := hv.mul hw
  simp only [mul_zero] at hp
  have hs : Tendsto (fun n => C n ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg (C n)) hb hp
  have hc : Tendsto C atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, sub_zero, Real.norm_eq_abs,
      Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hr
  have he (n : ℕ) : finiteQuadraticVariation (fun i => v n i + w n i) =
      finiteQuadraticVariation (v n) + 2 * C n + finiteQuadraticVariation (w n) := by
    simp only [finiteQuadraticVariation, C, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ht := (hv.add (hc.const_mul 2)).add hw
  simpa only [mul_zero, add_zero, ← he] using ht

end TimeTraps.Analysis
