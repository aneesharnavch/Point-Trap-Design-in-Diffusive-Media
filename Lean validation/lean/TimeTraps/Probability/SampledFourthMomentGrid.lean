module

public import TimeTraps.Probability.SampledFourthMomentTail
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentChaining

@[expose] public section

/-! Summable grid tail probabilities are derived from the countable fourth
increment condition. Borel–Cantelli produces one event controlling all
bounded time intervals and all sufficiently fine dyadic grids. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable {P : Measure Ω} [IsFiniteMeasure P] {X : ℕ → Ω → E} {C : ℝ}

def sampledFourthDyadicBad (X : ℕ → Ω → E) (R n : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range (R * 64 ^ n),
    {ω | (1 / 2 : ℝ) ^ n ≤ dist (X (Nat.pair n (k + 1)) ω)
      (X (Nat.pair n k) ω)}

omit [IsFiniteMeasure P] in
theorem sampledFourthDyadic_increment_tail
    (hi : ∀ s t, Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤ C * dist (brownianDyadicTime s) (brownianDyadicTime t) ^ 2) (n k : ℕ) :
    P.real {ω | (1 / 2 : ℝ) ^ n ≤ dist (X (Nat.pair n (k + 1)) ω)
      (X (Nat.pair n k) ω)} ≤ C * (1 / 256 : ℝ) ^ n := by
  have h := fourthMoment_dist_tail_of_bound (hi (Nat.pair n (k + 1)) (Nat.pair n k))
    (hb _ _) (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
  have he : dist (brownianDyadicTime (Nat.pair n (k + 1))) (brownianDyadicTime (Nat.pair n k)) =
      (1 / 64 : ℝ) ^ n := brownianDyadicTime_increment n k
  rw [he] at h
  convert h using 1
  rw [pow_right_comm (1 / 64 : ℝ) n 2, pow_right_comm (1 / 2 : ℝ) n 4,
    mul_div_assoc, ← div_pow]
  norm_num

omit [IsFiniteMeasure P] in
theorem sampledFourthDyadicBad_real_le
    (hi : ∀ s t, Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤ C * dist (brownianDyadicTime s) (brownianDyadicTime t) ^ 2) (R n : ℕ) :
    P.real (sampledFourthDyadicBad X R n) ≤ C * R * (1 / 4 : ℝ) ^ n := by
  calc
    _ ≤ ∑ k ∈ Finset.range (R * 64 ^ n), C * (1 / 256 : ℝ) ^ n :=
      (measureReal_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum (fun k _ => sampledFourthDyadic_increment_tail hi hb n k))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      calc
        (R : ℝ) * 64 ^ n * (C * (1 / 256 : ℝ) ^ n) =
            C * R * (64 ^ n * (1 / 256 : ℝ) ^ n) := by ring
        _ = _ := by rw [← mul_pow]; norm_num

theorem sampledFourthDyadicBad_summable
    (hi : ∀ s t, Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤ C * dist (brownianDyadicTime s) (brownianDyadicTime t) ^ 2) (R : ℕ) :
    (∑' n, P (sampledFourthDyadicBad X R n)) ≠ ∞ := by
  have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (C * (R : ℝ))
  apply ne_top_of_le_ne_top h.tsum_ofReal_ne_top
  apply ENNReal.tsum_le_tsum
  intro n
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (sampledFourthDyadicBad_real_le hi hb R n)

theorem sampledFourthDyadic_regular_ae
    (hc : ∀ᵐ ω ∂P, ∀ i j, brownianDyadicTime i = brownianDyadicTime j → X i ω = X j ω)
    (hi : ∀ s t, Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤ C * dist (brownianDyadicTime s) (brownianDyadicTime t) ^ 2) :
    ∀ᵐ ω ∂P, FourthDyadicRegular (fun i => X i ω) := by
  have hR (R : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∀ k < R * 64 ^ n, dist (X (Nat.pair n (k + 1)) ω)
        (X (Nat.pair n k) ω) < (1 / 2 : ℝ) ^ n := by
    filter_upwards [ae_eventually_notMem (sampledFourthDyadicBad_summable hi hb R)] with ω hω
    filter_upwards [hω] with n hn
    intro k hk
    apply lt_of_not_ge
    intro he
    exact hn (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨Finset.mem_range.mpr hk, he⟩⟩)
  filter_upwards [ae_all_iff.mpr hR, hc] with ω hω hωc
  exact ⟨hωc,
    fun R => eventually_atTop.mp (hω R)⟩

end TimeTraps.Probability
