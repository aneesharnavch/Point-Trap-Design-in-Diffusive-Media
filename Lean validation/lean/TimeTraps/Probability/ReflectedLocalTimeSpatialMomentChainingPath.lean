module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentChaining

@[expose] public section

/-! The geometric adjacent-grid bounds imply locally uniform convergence
and continuous paths in the complete target space. The step functions
need no continuity; the explicit neighboring-grid estimate controls the
limit at every pair of sufficiently close parameters. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem FourthDyadicRegular.dist_step_le {ω : ℕ → E} (hω : FourthDyadicRegular ω)
    {R N : ℕ} (hN : ∀ n ≥ N, ∀ k < R * 64 ^ n,
      dist (ω (Nat.pair n (k + 1))) (ω (Nat.pair n k)) < (1 / 2 : ℝ) ^ n)
    {n : ℕ} (hn : N ≤ n) {t : ℝ≥0} (ht : t.val ≤ R) :
    dist (fourthDyadicStep t n ω) (fourthDyadicPath t ω) ≤ 64 * (1 / 2 : ℝ) ^ n := by
  have hs : ∀ k, dist (fourthDyadicStep t (k + n) ω)
      (fourthDyadicStep t (k + 1 + n) ω) ≤
        (64 * (1 / 2 : ℝ) ^ (n + 1)) * (1 / 2 : ℝ) ^ k := by
    intro k
    have h := fourthDyadicStep_dist_le hω.consistent
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

theorem FourthDyadicRegular.tendstoUniformlyOn {ω : ℕ → E}
    (hω : FourthDyadicRegular ω) (R : ℕ) :
    TendstoUniformlyOn (fun n t => fourthDyadicStep t n ω)
      (fun t => fourthDyadicPath t ω) atTop (Iic (R : ℝ≥0)) := by
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

omit [CompleteSpace E] in
theorem fourthDyadicStep_close {ω : ℕ → E} {R n : ℕ}
    (hi : ∀ k < R * 64 ^ n,
      dist (ω (Nat.pair n (k + 1))) (ω (Nat.pair n k)) < (1 / 2 : ℝ) ^ n)
    {s t : ℝ≥0} (hs : s.val ≤ R) (ht : t.val ≤ R)
    (h : dist s t < (1 / 64 : ℝ) ^ n) :
    dist (fourthDyadicStep s n ω) (fourthDyadicStep t n ω) ≤ (1 / 2 : ℝ) ^ n := by
  have hc := brownianDyadicFloor_close n h
  have hbs := brownianDyadicFloor_le hs n
  have hbt := brownianDyadicFloor_le ht n
  unfold fourthDyadicStep
  rcases lt_trichotomy (brownianDyadicFloor s n) (brownianDyadicFloor t n) with hlt | heq | hgt
  · have he : brownianDyadicFloor t n = brownianDyadicFloor s n + 1 := by omega
    rw [he]
    simpa only [dist_comm] using
      (hi (brownianDyadicFloor s n) (by omega)).le
  · rw [heq, dist_self]
    positivity
  · have he : brownianDyadicFloor s n = brownianDyadicFloor t n + 1 := by omega
    rw [he]
    exact (hi (brownianDyadicFloor t n) (by omega)).le

theorem FourthDyadicRegular.uniformContinuousOn {ω : ℕ → E}
    (hω : FourthDyadicRegular ω) (R : ℕ) :
    UniformContinuousOn (fun t => fourthDyadicPath t ω) (Iic (R : ℝ≥0)) := by
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
  have h₂ := fourthDyadicStep_close (hN n hn) hs' ht' hst
  have h₃ := hω.dist_step_le hN hn ht'
  have htri := dist_triangle (fourthDyadicPath s ω)
    (fourthDyadicStep s n ω) (fourthDyadicPath t ω)
  have htri' := dist_triangle (fourthDyadicStep s n ω)
    (fourthDyadicStep t n ω) (fourthDyadicPath t ω)
  rw [dist_comm (fourthDyadicPath s ω) (fourthDyadicStep s n ω)] at htri
  linarith

theorem FourthDyadicRegular.continuous {ω : ℕ → E} (hω : FourthDyadicRegular ω) :
    Continuous (fun t => fourthDyadicPath t ω) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨R, hR⟩ := exists_nat_gt t.val
  exact (hω.uniformContinuousOn R).continuousOn.continuousAt
    (Iic_mem_nhds (by exact_mod_cast hR))

end TimeTraps.Probability
