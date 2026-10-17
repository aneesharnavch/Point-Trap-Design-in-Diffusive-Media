module

public import TimeTraps.Analysis.FiniteQuadraticVariation
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

/-! Uniform finite quadratic-variation stability. A perturbation whose
squared-increment sums vanish uniformly does not change a uniformly convergent
quadratic variation with bounded limiting function. -/

namespace TimeTraps.Analysis

open Filter Set
open scoped Topology

theorem real_tendstoUniformlyOn_iff_sub_tendsto {ι α : Type*}
    (F : ι → α → ℝ) (f : α → ℝ) (p : Filter ι) (s : Set α) :
    TendstoUniformlyOn F f p s ↔
      Tendsto (fun z : ι × α => F z.1 z.2 - f z.2) (p ×ˢ 𝓟 s) (𝓝 0) := by
  constructor
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    rw [eventually_prod_principal_iff]
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp h ε hε] with n hn x hx
    simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using hn x hx
  · intro h
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have he := Metric.tendsto_nhds.mp h ε hε
    rw [eventually_prod_principal_iff] at he
    filter_upwards [he] with n hn x hx
    simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using hn x hx

theorem finiteQuadraticVariation_uniform_sub_zero {α : Type*} (N : ℕ → ℕ)
    (v w : (n : ℕ) → α → Fin (N n + 1) → ℝ) (s : Set α)
    (hv : TendstoUniformlyOn (fun n x => finiteQuadraticVariation (v n x)) (fun _ => 0) atTop s)
    (hw : TendstoUniformlyOn (fun n x => finiteQuadraticVariation (w n x)) (fun _ => 0) atTop s) :
    TendstoUniformlyOn (fun n x => finiteQuadraticVariation (fun i => v n x i - w n x i))
      (fun _ => 0) atTop s := by
  rw [real_tendstoUniformlyOn_iff_sub_tendsto] at hv hw ⊢
  simp only [sub_zero] at hv hw ⊢
  have hb := (hv.const_mul 2).add (hw.const_mul 2)
  simp only [mul_zero, add_zero] at hb
  exact squeeze_zero (fun _ => finiteQuadraticVariation_nonneg _)
    (fun z => finiteQuadraticVariation_sub_le (v z.1 z.2) (w z.1 z.2)) hb

theorem finiteQuadraticVariation_uniform_affine {α : Type*} (N : ℕ → ℕ)
    (v : (n : ℕ) → α → Fin (N n + 1) → ℝ) (s : Set α) (A : α → ℝ) (a c : ℝ)
    (hv : TendstoUniformlyOn (fun n x => finiteQuadraticVariation (v n x)) A atTop s) :
    TendstoUniformlyOn (fun n x => finiteQuadraticVariation (fun i => c + a * v n x i))
      (fun x => a ^ 2 * A x) atTop s := by
  rw [real_tendstoUniformlyOn_iff_sub_tendsto] at hv ⊢
  have ht := hv.const_mul (a ^ 2)
  simp only [mul_zero] at ht
  simpa only [finiteQuadraticVariation_affine, mul_sub] using ht

theorem finiteQuadraticVariation_uniform_add {α : Type*} (N : ℕ → ℕ)
    (v w : (n : ℕ) → α → Fin (N n + 1) → ℝ) (s : Set α) (A : α → ℝ)
    (hv : TendstoUniformlyOn (fun n x => finiteQuadraticVariation (v n x)) A atTop s)
    (hw : TendstoUniformlyOn (fun n x => finiteQuadraticVariation (w n x)) (fun _ => 0) atTop s)
    (M : ℝ) (hA : ∀ x ∈ s, A x ≤ M) :
    TendstoUniformlyOn (fun n x => finiteQuadraticVariation (fun i => v n x i + w n x i))
      A atTop s := by
  let C (z : ℕ × α) : ℝ := ∑ i : Fin (N z.1),
    (v z.1 z.2 i.succ - v z.1 z.2 i.castSucc) *
      (w z.1 z.2 i.succ - w z.1 z.2 i.castSucc)
  have hb (z : ℕ × α) : C z ^ 2 ≤
      finiteQuadraticVariation (v z.1 z.2) * finiteQuadraticVariation (w z.1 z.2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hbound : ∀ᶠ z : ℕ × α in atTop ×ˢ 𝓟 s,
      finiteQuadraticVariation (v z.1 z.2) ≤ |M| + 1 := by
    rw [eventually_prod_principal_iff]
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hv 1 (by norm_num)] with n hn x hx
    have hd := hn x hx
    rw [Real.dist_eq, abs_sub_comm] at hd
    have he := (le_abs_self (finiteQuadraticVariation (v n x) - A x)).trans hd.le
    have ha := hA x hx
    have hm := le_abs_self M
    linarith
  rw [real_tendstoUniformlyOn_iff_sub_tendsto] at hv hw ⊢
  simp only [sub_zero] at hw
  have hz : Tendsto (fun z : ℕ × α => (|M| + 1) * finiteQuadraticVariation (w z.1 z.2))
      (atTop ×ˢ 𝓟 s) (𝓝 0) := by
    simpa only [mul_zero] using hw.const_mul (|M| + 1)
  have hs : Tendsto (fun z => C z ^ 2) (atTop ×ˢ 𝓟 s) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun z => sq_nonneg (C z))) ?_ hz
    filter_upwards [hbound] with z hz
    exact (hb z).trans (mul_le_mul_of_nonneg_right hz (finiteQuadraticVariation_nonneg _))
  have hc : Tendsto C (atTop ×ˢ 𝓟 s) (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, sub_zero, Real.norm_eq_abs,
      Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hr
  have he (z : ℕ × α) :
      finiteQuadraticVariation (fun i => v z.1 z.2 i + w z.1 z.2 i) - A z.2 =
        (finiteQuadraticVariation (v z.1 z.2) - A z.2) + 2 * C z +
          finiteQuadraticVariation (w z.1 z.2) := by
    have hid : finiteQuadraticVariation (fun i => v z.1 z.2 i + w z.1 z.2 i) =
        finiteQuadraticVariation (v z.1 z.2) + 2 * C z + finiteQuadraticVariation (w z.1 z.2) := by
      simp only [finiteQuadraticVariation, C, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hid]
    ring
  have ht := (hv.add (hc.const_mul 2)).add hw
  simpa only [mul_zero, add_zero, ← he] using ht

end TimeTraps.Analysis
