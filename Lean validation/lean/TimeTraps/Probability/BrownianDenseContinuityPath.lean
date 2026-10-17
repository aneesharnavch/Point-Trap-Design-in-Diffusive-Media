module

public import TimeTraps.Probability.BrownianDenseContinuityChain

@[expose] public section

/-! Locally uniform convergence and continuity of the measurable grid-limit
extension. These are properties of almost every sample of the constructed
dyadic Gaussian probability measure, not assumptions about Brownian paths. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem BrownianDyadicRegular.dist_step_le {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    {R N : ℕ} (hN : ∀ n ≥ N, ∀ k < R * 64 ^ n,
      |ω (Nat.pair n (k + 1)) - ω (Nat.pair n k)| < (1 / 2 : ℝ) ^ n)
    {n : ℕ} (hn : N ≤ n) {t : ℝ≥0} (ht : t.val ≤ R) :
    dist (brownianDyadicStep t n ω) (brownianDyadicPath t ω) ≤ 64 * (1 / 2 : ℝ) ^ n := by
  have hs : ∀ k, dist (brownianDyadicStep t (k + n) ω)
      (brownianDyadicStep t (k + 1 + n) ω) ≤
        (64 * (1 / 2 : ℝ) ^ (n + 1)) * (1 / 2 : ℝ) ^ k := by
    intro k
    have h := brownianDyadicStep_dist_le hω.consistent
      (hN (k + n + 1) (by omega)) ht
    simpa only [show k + 1 + n = k + n + 1 by omega,
      show k + n + 1 = n + 1 + k by omega, pow_add, mul_assoc] using h
  have h := dist_le_of_le_geometric_of_tendsto₀ (1 / 2 : ℝ)
    (64 * (1 / 2 : ℝ) ^ (n + 1)) (by norm_num) hs
    ((hω.tendsto t).comp (tendsto_add_atTop_nat n))
  simp only [zero_add] at h
  convert! h using 1
  rw [pow_succ]
  ring

theorem BrownianDyadicRegular.tendstoUniformlyOn {ω : ℕ → ℝ}
    (hω : BrownianDyadicRegular ω) (R : ℕ) :
    TendstoUniformlyOn (fun n t => brownianDyadicStep t n ω)
      (fun t => brownianDyadicPath t ω) atTop (Iic (R : ℝ≥0)) := by
  obtain ⟨N, hN⟩ := hω.increments R
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hp : Tendsto (fun n : ℕ => 64 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 64
  filter_upwards [eventually_ge_atTop N, hp.eventually (gt_mem_nhds hε)] with n hn he
  intro t ht
  rw [dist_comm]
  exact (hω.dist_step_le hN hn (by exact_mod_cast ht)).trans_lt he

theorem brownianDyadicFloor_close {s t : ℝ≥0} (n : ℕ)
    (h : dist s t < (1 / 64 : ℝ) ^ n) :
    brownianDyadicFloor s n ≤ brownianDyadicFloor t n + 1 ∧
      brownianDyadicFloor t n ≤ brownianDyadicFloor s n + 1 := by
  have hp : 0 < (64 : ℝ) ^ n := by positivity
  change |s.val - t.val| < (1 / 64 : ℝ) ^ n at h
  have hm := mul_lt_mul_of_pos_right h hp
  have he : (1 / 64 : ℝ) ^ n * 64 ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [he] at hm
  have hd : |s.val * (64 : ℝ) ^ n - t.val * (64 : ℝ) ^ n| < 1 := by
    rw [← sub_mul, abs_mul, abs_of_pos hp]
    exact hm
  have hs : 0 ≤ s.val * (64 : ℝ) ^ n := mul_nonneg s.coe_nonneg hp.le
  have ht : 0 ≤ t.val * (64 : ℝ) ^ n := mul_nonneg t.coe_nonneg hp.le
  have hs' := Nat.lt_floor_add_one (s.val * (64 : ℝ) ^ n)
  have ht' := Nat.lt_floor_add_one (t.val * (64 : ℝ) ^ n)
  change ⌊s.val * (64 : ℝ) ^ n⌋₊ ≤ ⌊t.val * (64 : ℝ) ^ n⌋₊ + 1 ∧
    ⌊t.val * (64 : ℝ) ^ n⌋₊ ≤ ⌊s.val * (64 : ℝ) ^ n⌋₊ + 1
  constructor
  · apply Nat.le_of_lt_succ
    apply (Nat.floor_lt hs).mpr
    push_cast
    linarith [(abs_lt.mp hd).2]
  · apply Nat.le_of_lt_succ
    apply (Nat.floor_lt ht).mpr
    push_cast
    linarith [(abs_lt.mp hd).1]

theorem brownianDyadicStep_close {ω : ℕ → ℝ} {R n : ℕ}
    (hi : ∀ k < R * 64 ^ n,
      |ω (Nat.pair n (k + 1)) - ω (Nat.pair n k)| < (1 / 2 : ℝ) ^ n)
    {s t : ℝ≥0} (hs : s.val ≤ R) (ht : t.val ≤ R)
    (h : dist s t < (1 / 64 : ℝ) ^ n) :
    dist (brownianDyadicStep s n ω) (brownianDyadicStep t n ω) ≤ (1 / 2 : ℝ) ^ n := by
  have hc := brownianDyadicFloor_close n h
  have hbs := brownianDyadicFloor_le hs n
  have hbt := brownianDyadicFloor_le ht n
  unfold brownianDyadicStep
  rcases lt_trichotomy (brownianDyadicFloor s n) (brownianDyadicFloor t n) with hlt | heq | hgt
  · have he : brownianDyadicFloor t n = brownianDyadicFloor s n + 1 := by omega
    rw [he]
    simpa only [Real.dist_eq, abs_sub_comm] using
      (hi (brownianDyadicFloor s n) (by omega)).le
  · rw [heq, dist_self]
    positivity
  · have he : brownianDyadicFloor s n = brownianDyadicFloor t n + 1 := by omega
    rw [he]
    exact (hi (brownianDyadicFloor t n) (by omega)).le

theorem BrownianDyadicRegular.uniformContinuousOn {ω : ℕ → ℝ}
    (hω : BrownianDyadicRegular ω) (R : ℕ) :
    UniformContinuousOn (fun t => brownianDyadicPath t ω) (Iic (R : ℝ≥0)) := by
  obtain ⟨N, hN⟩ := hω.increments R
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  have hp : Tendsto (fun n : ℕ => 129 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 129
  obtain ⟨n, hn, he⟩ := ((eventually_ge_atTop N).and
    (hp.eventually (gt_mem_nhds hε))).exists
  refine ⟨(1 / 64 : ℝ) ^ n, by positivity, ?_⟩
  intro s hs t ht hst
  have hs' : s.val ≤ R := by exact_mod_cast hs
  have ht' : t.val ≤ R := by exact_mod_cast ht
  have h₁ := hω.dist_step_le hN hn hs'
  have h₂ := brownianDyadicStep_close (hN n hn) hs' ht' hst
  have h₃ := hω.dist_step_le hN hn ht'
  have htri := dist_triangle (brownianDyadicPath s ω)
    (brownianDyadicStep s n ω) (brownianDyadicPath t ω)
  have htri' := dist_triangle (brownianDyadicStep s n ω)
    (brownianDyadicStep t n ω) (brownianDyadicPath t ω)
  rw [dist_comm (brownianDyadicPath s ω) (brownianDyadicStep s n ω)] at htri
  linarith

theorem BrownianDyadicRegular.continuous {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) :
    Continuous (fun t => brownianDyadicPath t ω) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨R, hR⟩ := exists_nat_gt t.val
  exact (hω.uniformContinuousOn R).continuousOn.continuousAt
    (Iic_mem_nhds (by exact_mod_cast hR))

theorem brownianDyadicPath_continuous_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, Continuous (fun t => brownianDyadicPath t ω) :=
  brownianDyadic_regular_ae.mono (fun _ hω => hω.continuous)

theorem brownianDyadicPath_locally_uniform_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ R : ℕ,
      TendstoUniformlyOn (fun n t => brownianDyadicStep t n ω)
        (fun t => brownianDyadicPath t ω) atTop (Iic (R : ℝ≥0)) ∧
      UniformContinuousOn (fun t => brownianDyadicPath t ω) (Iic (R : ℝ≥0)) :=
  brownianDyadic_regular_ae.mono (fun _ hω R => ⟨hω.tendstoUniformlyOn R, hω.uniformContinuousOn R⟩)

end TimeTraps.Probability
