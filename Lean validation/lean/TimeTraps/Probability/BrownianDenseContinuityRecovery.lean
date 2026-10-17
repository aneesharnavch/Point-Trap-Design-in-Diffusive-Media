module

public import TimeTraps.Probability.BrownianDenseContinuityPath

@[expose] public section

/-! The continuous limit recovers every coordinate of the constructed dense
Gaussian realization simultaneously almost surely. Hence its finite laws
on this dense set are exactly the original projective laws. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem brownianDyadicFloor_at_grid (n k l : ℕ) :
    brownianDyadicFloor (brownianDyadicTime (Nat.pair n k)) (n + l) = k * 64 ^ l := by
  unfold brownianDyadicFloor
  rw [brownianDyadicTime_pair]
  change ⌊((k : ℝ) * (1 / 64 : ℝ) ^ n) * (64 : ℝ) ^ (n + l)⌋₊ = k * 64 ^ l
  have he : ((k : ℝ) * (1 / 64 : ℝ) ^ n) * (64 : ℝ) ^ (n + l) =
      ((k * 64 ^ l : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    calc
      _ = ((k : ℝ) * 64 ^ l) * ((1 / 64 : ℝ) ^ n * 64 ^ n) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  rw [he, Nat.floor_natCast]

theorem brownianDyadicTime_refine_many (n k l : ℕ) :
    brownianDyadicTime (Nat.pair (n + l) (k * 64 ^ l)) = brownianDyadicTime (Nat.pair n k) := by
  rw [brownianDyadicTime_pair, brownianDyadicTime_pair]
  apply NNReal.eq
  change ((k * 64 ^ l : ℕ) : ℝ) * (1 / 64 : ℝ) ^ (n + l) = k * (1 / 64 : ℝ) ^ n
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  calc
    _ = ((k : ℝ) * (1 / 64 : ℝ) ^ n) * (64 ^ l * (1 / 64 : ℝ) ^ l) := by ring
    _ = _ := by rw [← mul_pow]; norm_num

theorem BrownianDyadicRegular.path_eq_coordinate {ω : ℕ → ℝ}
    (hω : BrownianDyadicRegular ω) (i : ℕ) : brownianDyadicPath (brownianDyadicTime i) ω = ω i := by
  obtain ⟨n, k, rfl⟩ : ∃ n k, Nat.pair n k = i :=
    ⟨(Nat.unpair i).1, (Nat.unpair i).2, Nat.pair_unpair i⟩
  have he (l : ℕ) : brownianDyadicStep (brownianDyadicTime (Nat.pair n k)) (l + n) ω =
      ω (Nat.pair n k) := by
    rw [Nat.add_comm l n]
    unfold brownianDyadicStep
    rw [brownianDyadicFloor_at_grid]
    exact hω.consistent _ _ (brownianDyadicTime_refine_many n k l)
  apply tendsto_nhds_unique ((hω.tendsto (brownianDyadicTime (Nat.pair n k))).comp
    (tendsto_add_atTop_nat n))
  simpa only [Function.comp_def, he] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ω (Nat.pair n k)) atTop (𝓝 (ω (Nat.pair n k))))

theorem brownianDyadicPath_recovers_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ℕ, brownianDyadicPath (brownianDyadicTime i) ω = ω i :=
  brownianDyadic_regular_ae.mono (fun _ hω => hω.path_eq_coordinate)

theorem brownianDyadicPath_grid_hasLaw (I : Finset ℕ) :
    HasLaw (fun ω : ℕ → ℝ => fun i : I => brownianDyadicPath (brownianDyadicTime i) ω)
      (brownianSequenceFamily brownianDyadicTime I) brownianDyadicMeasure := by
  apply (brownianSequence_hasLaw brownianDyadicTime I).congr
  filter_upwards [brownianDyadicPath_recovers_ae] with ω hω
  exact funext (fun i => hω i)

theorem brownianDyadicPath_start_zero :
    ∀ᵐ ω ∂brownianDyadicMeasure, brownianDyadicPath 0 ω = 0 := by
  have h := brownianSequence_eval_hasLaw brownianDyadicTime (Nat.pair 0 0)
  rw [brownianDyadicTime_pair, Nat.cast_zero, zero_mul, gaussianReal_zero_var] at h
  filter_upwards [brownianDyadicPath_recovers_ae, h.ae_eq_of_dirac] with ω hω hzero
  have he := hω (Nat.pair 0 0)
  simpa only [brownianDyadicTime_pair, Nat.cast_zero, zero_mul, hzero] using he

end TimeTraps.Probability
