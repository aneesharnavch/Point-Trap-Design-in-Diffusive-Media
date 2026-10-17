module

public import TimeTraps.Probability.BrownianMartingaleMoments

@[expose] public section

/-! Exact finite-partition moments of squared Brownian increments. The
variance sum uses the proved independence of disjoint increments; repeated
partition points and an empty partition are permitted. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_increment_square_memLp (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    MemLp (fun ω => (B t ω - B s ω) ^ 2) 2 P := by
  have h := brownian_increment_memLp hB s t 4 (by norm_num)
  convert! h.norm_rpow_div 2 using 1 <;> norm_num [Real.norm_eq_abs, Real.rpow_two]
  apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).mpr
  norm_num

theorem brownian_increment_square_variance (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    Var[fun ω => (B t ω - B s ω) ^ 2; P] = 2 * |t.val - s.val| ^ 2 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [variance_eq_sub (brownian_increment_square_memLp hB s t)]
  change (∫ ω, ((B t ω - B s ω) ^ 2) ^ 2 ∂P) -
    (∫ ω, (B t ω - B s ω) ^ 2 ∂P) ^ 2 = _
  simp only [← pow_mul, Nat.reduceMul]
  rw [brownian_increment_fourth_moment hB s t, brownian_increment_second_moment hB s t]
  ring

noncomputable def brownianPartitionQV (B : ℝ≥0 → Ω → ℝ) {N : ℕ}
    (τ : Fin (N + 1) → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin N, (B (τ i.succ) ω - B (τ i.castSucc) ω) ^ 2

theorem brownianPartitionQV_memLp (hB : IsPreBrownianReal B P) {N : ℕ}
    (τ : Fin (N + 1) → ℝ≥0) : MemLp (brownianPartitionQV B τ) 2 P :=
  memLp_finsetSum _ (fun i _ => brownian_increment_square_memLp hB (τ i.castSucc) (τ i.succ))

theorem brownianPartitionQV_mean (hB : IsPreBrownianReal B P) {N : ℕ}
    (τ : Fin (N + 1) → ℝ≥0) :
    (∫ ω, brownianPartitionQV B τ ω ∂P) = ∑ i : Fin N, |(τ i.succ).val - (τ i.castSucc).val| := by
  calc
    _ = ∑ i : Fin N, ∫ ω, (B (τ i.succ) ω - B (τ i.castSucc) ω) ^ 2 ∂P :=
      integral_finsetSum _ (fun i _ => brownian_increment_integrable_sq hB (τ i.castSucc) (τ i.succ))
    _ = _ := Finset.sum_congr rfl (fun i _ => brownian_increment_second_moment hB _ _)

theorem brownianPartitionQV_variance (hB : IsPreBrownianReal B P) {N : ℕ}
    (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) :
    Var[brownianPartitionQV B τ; P] =
      ∑ i : Fin N, 2 * |(τ i.succ).val - (τ i.castSucc).val| ^ 2 := by
  have hind := (hB.hasIndepIncrements N τ hτ).comp (fun _ (x : ℝ) => x ^ 2) (by fun_prop)
  have he : brownianPartitionQV B τ =
      ∑ i : Fin N, (fun ω => (B (τ i.succ) ω - B (τ i.castSucc) ω) ^ 2) := by
    funext ω
    simp only [brownianPartitionQV, Finset.sum_apply]
  rw [he]
  have hv := IndepFun.variance_sum (s := Finset.univ)
    (X := fun i : Fin N => fun ω => (B (τ i.succ) ω - B (τ i.castSucc) ω) ^ 2)
    (fun i _ => brownian_increment_square_memLp hB (τ i.castSucc) (τ i.succ))
    (fun i _ j _ hij => hind.indepFun hij)
  exact hv.trans (Finset.sum_congr rfl (fun i _ => brownian_increment_square_variance hB _ _))

end TimeTraps.Probability
