module

public import TimeTraps.Probability.BrownianDenseMoments
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Data.Nat.Pairing

@[expose] public section

/-! The probabilistic grid step of the continuous-path construction. These
are dyadic grids at levels `6n`, with mesh `64⁻ⁿ`. Their actual countable
Gaussian realization almost surely has every adjacent increment on each
bounded interval smaller than `2⁻ⁿ` for all sufficiently large `n`.
Passing from this estimate to a locally uniform continuous extension is a
separate deterministic step. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable def brownianDyadicTime (i : ℕ) : ℝ≥0 :=
  (Nat.unpair i).2 * (1 / 64 : ℝ≥0) ^ (Nat.unpair i).1

theorem brownianDyadicTime_pair (n k : ℕ) :
    brownianDyadicTime (Nat.pair n k) = k * (1 / 64 : ℝ≥0) ^ n := by
  simp [brownianDyadicTime]

theorem brownianDyadicTime_increment (n k : ℕ) :
    |(brownianDyadicTime (Nat.pair n (k + 1))).val -
      (brownianDyadicTime (Nat.pair n k)).val| = (1 / 64 : ℝ) ^ n := by
  rw [brownianDyadicTime_pair, brownianDyadicTime_pair]
  change |((k + 1 : ℕ) : ℝ) * (1 / 64 : ℝ) ^ n - k * (1 / 64 : ℝ) ^ n| = _
  rw [Nat.cast_add, Nat.cast_one]
  rw [show ((k : ℝ) + 1) * (1 / 64 : ℝ) ^ n - k * (1 / 64 : ℝ) ^ n =
    (1 / 64 : ℝ) ^ n by ring, abs_of_nonneg (by positivity)]

theorem brownianDyadicTime_dense : DenseRange brownianDyadicTime := by
  apply Metric.denseRange_iff.mpr
  intro t ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 64 : ℝ) < 1)
  let a : ℝ := (1 / 64 : ℝ) ^ n
  have ha : 0 < a := by positivity
  let k := ⌊t.val / a⌋₊
  have hk₁ : (k : ℝ) * a ≤ t.val :=
    (le_div_iff₀ ha).mp (Nat.floor_le (div_nonneg t.coe_nonneg ha.le))
  have hk₂ : t.val < ((k : ℝ) + 1) * a :=
    (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one (t.val / a))
  refine ⟨Nat.pair n k, ?_⟩
  change |t.val - (brownianDyadicTime (Nat.pair n k)).val| < ε
  rw [brownianDyadicTime_pair]
  change |t.val - (k : ℝ) * a| < ε
  rw [abs_of_nonneg (sub_nonneg.mpr hk₁)]
  change a < ε at hn
  linarith

noncomputable def brownianDyadicMeasure : Measure (ℕ → ℝ) :=
  brownianSequenceMeasure brownianDyadicTime

instance brownianDyadicMeasure_probability : IsProbabilityMeasure brownianDyadicMeasure :=
  brownianSequenceMeasure_probability brownianDyadicTime

def brownianDyadicBad (R n : ℕ) : Set (ℕ → ℝ) :=
  ⋃ k ∈ Finset.range (R * 64 ^ n),
    {ω | (1 / 2 : ℝ) ^ n ≤ |ω (Nat.pair n (k + 1)) - ω (Nat.pair n k)|}

theorem brownianDyadic_increment_tail (n k : ℕ) :
    brownianDyadicMeasure.real
      {ω | (1 / 2 : ℝ) ^ n ≤ |ω (Nat.pair n (k + 1)) - ω (Nat.pair n k)|} ≤
      3 * (1 / 256 : ℝ) ^ n := by
  have h := brownianSequence_increment_tail_fourth brownianDyadicTime
    (Nat.pair n (k + 1)) (Nat.pair n k) (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
  rw [brownianDyadicTime_increment] at h
  have he : 3 * ((1 / 64 : ℝ) ^ n) ^ 2 / ((1 / 2 : ℝ) ^ n) ^ 4 =
      3 * (1 / 256 : ℝ) ^ n := by
    rw [pow_right_comm (1 / 64 : ℝ) n 2, pow_right_comm (1 / 2 : ℝ) n 4,
      mul_div_assoc, ← div_pow]
    norm_num
  exact h.trans_eq he

theorem brownianDyadicBad_real_le (R n : ℕ) :
    brownianDyadicMeasure.real (brownianDyadicBad R n) ≤ 3 * R * (1 / 4 : ℝ) ^ n := by
  calc
    _ ≤ ∑ k ∈ Finset.range (R * 64 ^ n), 3 * (1 / 256 : ℝ) ^ n :=
      (measureReal_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum (fun k _ => brownianDyadic_increment_tail n k))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      calc
        (R : ℝ) * 64 ^ n * (3 * (1 / 256 : ℝ) ^ n) =
            3 * R * (64 ^ n * (1 / 256 : ℝ) ^ n) := by ring
        _ = _ := by rw [← mul_pow]; norm_num

theorem brownianDyadicBad_measure_le (R n : ℕ) :
    brownianDyadicMeasure (brownianDyadicBad R n) ≤
      ENNReal.ofReal (3 * R * (1 / 4 : ℝ) ^ n) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (brownianDyadicBad_real_le R n)

theorem brownianDyadicBad_summable (R : ℕ) :
    (∑' n, brownianDyadicMeasure (brownianDyadicBad R n)) ≠ ∞ := by
  have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (3 * (R : ℝ))
  exact ne_top_of_le_ne_top h.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum (brownianDyadicBad_measure_le R))

theorem brownianDyadic_increments_eventually (R : ℕ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ᶠ n in atTop,
      ∀ k < R * 64 ^ n,
        |ω (Nat.pair n (k + 1)) - ω (Nat.pair n k)| < (1 / 2 : ℝ) ^ n := by
  have h := ae_eventually_notMem (brownianDyadicBad_summable R)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  intro k hk
  apply lt_of_not_ge
  intro he
  exact hn (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨Finset.mem_range.mpr hk, he⟩⟩)

theorem brownianDyadic_increments_locally_eventually :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ R : ℕ, ∀ᶠ n in atTop,
      ∀ k < R * 64 ^ n,
        |ω (Nat.pair n (k + 1)) - ω (Nat.pair n k)| < (1 / 2 : ℝ) ^ n :=
  ae_all_iff.mpr brownianDyadic_increments_eventually

end TimeTraps.Probability
