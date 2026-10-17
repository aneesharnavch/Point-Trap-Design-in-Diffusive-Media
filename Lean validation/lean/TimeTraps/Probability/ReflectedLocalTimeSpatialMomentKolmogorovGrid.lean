module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentKolmogorovTail
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentChaining

@[expose] public section

/-! Summable grid tail probabilities are derived from the actual fourth
increment condition. Borel–Cantelli produces one event controlling all
bounded index intervals and all sufficiently fine dyadic grids. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → E} {C : ℝ}

def fourthDyadicBad (X : ℝ≥0 → Ω → E) (R n : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range (R * 64 ^ n),
    {ω | (1 / 2 : ℝ) ^ n ≤ dist (X (brownianDyadicTime (Nat.pair n (k + 1))) ω)
      (X (brownianDyadicTime (Nat.pair n k)) ω)}

omit [IsFiniteMeasure P] in
theorem fourthDyadic_increment_tail
    (hi : ∀ s t, Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤ C * dist s t ^ 2) (n k : ℕ) :
    P.real {ω | (1 / 2 : ℝ) ^ n ≤ dist (X (brownianDyadicTime (Nat.pair n (k + 1))) ω)
      (X (brownianDyadicTime (Nat.pair n k)) ω)} ≤ C * (1 / 256 : ℝ) ^ n := by
  have h := fourthMoment_increment_tail (hi (brownianDyadicTime (Nat.pair n (k + 1)))
    (brownianDyadicTime (Nat.pair n k))) (hb _ _) (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
  have he : dist (brownianDyadicTime (Nat.pair n (k + 1))) (brownianDyadicTime (Nat.pair n k)) =
      (1 / 64 : ℝ) ^ n := brownianDyadicTime_increment n k
  rw [he] at h
  convert h using 1
  rw [pow_right_comm (1 / 64 : ℝ) n 2, pow_right_comm (1 / 2 : ℝ) n 4,
    mul_div_assoc, ← div_pow]
  norm_num

omit [IsFiniteMeasure P] in
theorem fourthDyadicBad_real_le
    (hi : ∀ s t, Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤ C * dist s t ^ 2) (R n : ℕ) :
    P.real (fourthDyadicBad X R n) ≤ C * R * (1 / 4 : ℝ) ^ n := by
  calc
    _ ≤ ∑ k ∈ Finset.range (R * 64 ^ n), C * (1 / 256 : ℝ) ^ n :=
      (measureReal_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum (fun k _ => fourthDyadic_increment_tail hi hb n k))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      calc
        (R : ℝ) * 64 ^ n * (C * (1 / 256 : ℝ) ^ n) =
            C * R * (64 ^ n * (1 / 256 : ℝ) ^ n) := by ring
        _ = _ := by rw [← mul_pow]; norm_num

theorem fourthDyadicBad_summable
    (hi : ∀ s t, Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤ C * dist s t ^ 2) (R : ℕ) :
    (∑' n, P (fourthDyadicBad X R n)) ≠ ∞ := by
  have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (C * (R : ℝ))
  apply ne_top_of_le_ne_top h.tsum_ofReal_ne_top
  apply ENNReal.tsum_le_tsum
  intro n
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (fourthDyadicBad_real_le hi hb R n)

theorem fourthDyadic_regular_ae
    (hi : ∀ s t, Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤ C * dist s t ^ 2) :
    ∀ᵐ ω ∂P, FourthDyadicRegular (fun i => X (brownianDyadicTime i) ω) := by
  have hR (R : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∀ k < R * 64 ^ n, dist (X (brownianDyadicTime (Nat.pair n (k + 1))) ω)
        (X (brownianDyadicTime (Nat.pair n k)) ω) < (1 / 2 : ℝ) ^ n := by
    filter_upwards [ae_eventually_notMem (fourthDyadicBad_summable hi hb R)] with ω hω
    filter_upwards [hω] with n hn
    intro k hk
    apply lt_of_not_ge
    intro he
    exact hn (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨Finset.mem_range.mpr hk, he⟩⟩)
  filter_upwards [ae_all_iff.mpr hR] with ω hω
  exact ⟨fun i j hij => congrArg (fun t => X t ω) hij,
    fun R => eventually_atTop.mp (hω R)⟩

end TimeTraps.Probability
