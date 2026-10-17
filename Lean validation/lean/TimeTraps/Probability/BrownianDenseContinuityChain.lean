module

public import TimeTraps.Probability.BrownianDenseContinuityGrid
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

@[expose] public section

/-! Deterministic chaining for the almost-sure grid event, and a measurable
pointwise extension defined by limits of the actual sampled coordinates. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

structure BrownianDyadicRegular (ω : ℕ → ℝ) : Prop where
  consistent : ∀ i j, brownianDyadicTime i = brownianDyadicTime j → ω i = ω j
  increments : ∀ R : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ k < R * 64 ^ n,
    |ω (Nat.pair n (k + 1)) - ω (Nat.pair n k)| < (1 / 2 : ℝ) ^ n

theorem brownianDyadic_regular_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, BrownianDyadicRegular ω := by
  filter_upwards [brownianSequence_consistent_ae brownianDyadicTime,
    brownianDyadic_increments_locally_eventually] with ω hc hi
  exact ⟨hc, fun R => eventually_atTop.mp (hi R)⟩

noncomputable def brownianDyadicFloor (t : ℝ≥0) (n : ℕ) : ℕ :=
  ⌊t.val * (64 : ℝ) ^ n⌋₊

noncomputable def brownianDyadicStep (t : ℝ≥0) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ω (Nat.pair n (brownianDyadicFloor t n))

noncomputable def brownianDyadicPath (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  limUnder atTop (fun n => brownianDyadicStep t n ω)

theorem brownianDyadicFloor_le {t : ℝ≥0} {R : ℕ} (ht : t.val ≤ R) (n : ℕ) :
    brownianDyadicFloor t n ≤ R * 64 ^ n := by
  apply Nat.floor_le_of_le
  exact_mod_cast mul_le_mul_of_nonneg_right ht (by positivity : (0 : ℝ) ≤ 64 ^ n)

theorem brownianDyadicFloor_refine (t : ℝ≥0) (n : ℕ) :
    64 * brownianDyadicFloor t n ≤ brownianDyadicFloor t (n + 1) ∧
      brownianDyadicFloor t (n + 1) < 64 * brownianDyadicFloor t n + 64 := by
  change 64 * ⌊t.val * (64 : ℝ) ^ n⌋₊ ≤ ⌊t.val * (64 : ℝ) ^ (n + 1)⌋₊ ∧
    ⌊t.val * (64 : ℝ) ^ (n + 1)⌋₊ < 64 * ⌊t.val * (64 : ℝ) ^ n⌋₊ + 64
  have hx : 0 ≤ t.val * (64 : ℝ) ^ n := mul_nonneg t.coe_nonneg (by positivity)
  have hx' : 0 ≤ t.val * (64 : ℝ) ^ (n + 1) := mul_nonneg t.coe_nonneg (by positivity)
  have h₁ := Nat.floor_le hx
  have h₂ := Nat.lt_floor_add_one (t.val * (64 : ℝ) ^ n)
  constructor
  · apply (Nat.le_floor_iff hx').mpr
    push_cast
    rw [pow_succ]
    nlinarith
  · apply (Nat.floor_lt hx').mpr
    push_cast
    rw [pow_succ]
    nlinarith

theorem brownianDyadicTime_refine (n k : ℕ) :
    brownianDyadicTime (Nat.pair (n + 1) (64 * k)) = brownianDyadicTime (Nat.pair n k) := by
  rw [brownianDyadicTime_pair, brownianDyadicTime_pair]
  apply NNReal.eq
  change ((64 * k : ℕ) : ℝ) * (1 / 64 : ℝ) ^ (n + 1) = k * (1 / 64 : ℝ) ^ n
  rw [Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  ring

theorem brownianDyadicStep_dist_le {ω : ℕ → ℝ}
    (hc : ∀ i j, brownianDyadicTime i = brownianDyadicTime j → ω i = ω j)
    {R n : ℕ} (hi : ∀ k < R * 64 ^ (n + 1),
      |ω (Nat.pair (n + 1) (k + 1)) - ω (Nat.pair (n + 1) k)| <
        (1 / 2 : ℝ) ^ (n + 1)) {t : ℝ≥0} (ht : t.val ≤ R) :
    dist (brownianDyadicStep t n ω) (brownianDyadicStep t (n + 1) ω) ≤
      64 * (1 / 2 : ℝ) ^ (n + 1) := by
  have hr := brownianDyadicFloor_refine t n
  have hb := brownianDyadicFloor_le ht (n + 1)
  have he := hc _ _ (brownianDyadicTime_refine n (brownianDyadicFloor t n))
  unfold brownianDyadicStep
  rw [← he]
  calc
    _ ≤ ∑ k ∈ Finset.Ico (64 * brownianDyadicFloor t n) (brownianDyadicFloor t (n + 1)),
        (1 / 2 : ℝ) ^ (n + 1) := by
      apply dist_le_Ico_sum_of_dist_le (f := fun k => ω (Nat.pair (n + 1) k))
        (d := fun _ => (1 / 2 : ℝ) ^ (n + 1)) hr.1
      intro k _ hk
      simpa only [Real.dist_eq, abs_sub_comm] using (hi k (hk.trans_le hb)).le
    _ ≤ 64 * (1 / 2 : ℝ) ^ (n + 1) := by
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show brownianDyadicFloor t (n + 1) - 64 * brownianDyadicFloor t n ≤ 64
        by omega)

theorem BrownianDyadicRegular.cauchySeq {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (t : ℝ≥0) : CauchySeq (fun n => brownianDyadicStep t n ω) := by
  obtain ⟨R, hR⟩ := exists_nat_gt t.val
  obtain ⟨N, hN⟩ := hω.increments R
  apply (cauchySeq_shift N).mp
  apply cauchySeq_of_le_geometric (1 / 2 : ℝ) (64 * (1 / 2 : ℝ) ^ (N + 1))
    (by norm_num)
  intro n
  have h := brownianDyadicStep_dist_le hω.consistent (hN (n + N + 1) (by omega)) hR.le
  simpa only [show n + 1 + N = n + N + 1 by omega,
    show n + N + 1 = N + 1 + n by omega, pow_add, mul_assoc] using h

theorem BrownianDyadicRegular.tendsto {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (t : ℝ≥0) : Tendsto (fun n => brownianDyadicStep t n ω) atTop
      (𝓝 (brownianDyadicPath t ω)) :=
  (hω.cauchySeq t).tendsto_limUnder

theorem brownianDyadicPath_measurable (t : ℝ≥0) : Measurable (brownianDyadicPath t) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  exact (measurable_pi_apply _).stronglyMeasurable

theorem brownianDyadicPath_tendsto_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0,
      Tendsto (fun n => brownianDyadicStep t n ω) atTop (𝓝 (brownianDyadicPath t ω)) := by
  exact brownianDyadic_regular_ae.mono (fun _ hω => hω.tendsto)

end TimeTraps.Probability
