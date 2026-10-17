module

public import TimeTraps.Probability.BrownianIntegralFourthEnergyLimit
public import TimeTraps.Probability.BrownianIntegralFourthLimit

@[expose] public section

/-! The existing Brownian integral of a bounded coefficient with countably
many possible discontinuities satisfies the actual fourth-energy bound.
The dyadic sums converge in the original integral's L2 space; Fatou derives
fourth integrability and the estimate without a BDG assumption. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {C : Set ℝ} {M : ℝ≥0}

theorem brownianCountableIntegral_fourth_energy (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T : ℝ≥0) :
    MemLp (brownianCountableIntegral hB hBm hjoint hg hb hC hc T) 4 P ∧
      (∫ ω, brownianCountableIntegral hB hBm hjoint hg hb hC hc T ω ^ 4 ∂P) ≤
        150 * ∫ ω, (∫ r, brownianSquareProcess (fun t ω => g (B t ω)) T (r, ω) ^ 2) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let H : ℝ≥0 → Ω → ℝ := fun t ω => g (B t ω)
  let F : ℕ → Lp ℝ 2 P := fun n => brownianIntegral hB.toIsPreBrownianReal
    (brownianCountableStepIntegrand hB.toIsPreBrownianReal hBm hg hb T n)
  let G := brownianCountableIntegral hB hBm hjoint hg hb hC hc T
  have hcoef (n : ℕ) (i : Fin (2 ^ n)) :
      MemLp (H (brownianDyadicGrid T n i.castSucc)) 4 P :=
    MemLp.of_bound (hg.comp (hBm _)).aestronglyMeasurable M.val
      (Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hb (B (brownianDyadicGrid T n i.castSucc) ω)))
  have had (n : ℕ) (i : Fin (2 ^ n)) :
      StronglyMeasurable[brownianNaturalFiltration B hBm (brownianDyadicGrid T n i.castSucc)]
        (H (brownianDyadicGrid T n i.castSucc)) := brownianCountable_coefficient_adapted hBm hg _
  have hF4 (n : ℕ) : MemLp (F n) 4 P :=
    (brownianStepIntegral_fourth_memLp hB.toIsPreBrownianReal hBm (brownianDyadicGrid T n)
      (brownianDyadicGrid_monotone T n) (fun i => H (brownianDyadicGrid T n i.castSucc)) (had n) (hcoef n)).ae_eq
      (brownianCountableStep_integral_ae hB.toIsPreBrownianReal hBm hg hb T n).symm
  have hbound (n : ℕ) : (∫ ω, F n ω ^ 4 ∂P) ≤
      150 * ∫ ω, (∫ r, brownianSquareStepProcess H T n (r, ω) ^ 2) ^ 2 ∂P := by
    have h := brownianIntegral_fourth_energy_bound_of_step_representation hB.toIsPreBrownianReal hBm
      (brownianDyadicGrid T n) (brownianDyadicGrid_monotone T n)
      (fun i => H (brownianDyadicGrid T n i.castSucc)) (had n) (hcoef n)
      (brownianCountableStepIntegrand hB.toIsPreBrownianReal hBm hg hb T n)
      (brownianCountableStep_integral_ae hB.toIsPreBrownianReal hBm hg hb T n)
    simpa only [brownian_fourth_step_energy_eq] using h
  have hconv : Tendsto F atTop (𝓝 G) := brownianCountableStepIntegral_tendsto hB hBm hjoint hg hb hC hc T
  have henergy := brownian_fourth_step_energy_square_tendsto (hg.comp hjoint) (fun t ω => hb (B t ω)) T
    (brownianCountable_step_tendsto_ae hB hjoint hC hc T)
  exact brownian_fourth_bound_of_L2_tendsto
    (mul_nonneg (by norm_num) (integral_nonneg (fun ω => sq_nonneg _))) hF4 hconv hbound
    (henergy.const_mul 150)

theorem brownianCountableIntegral_fourth_energy_literal (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T : ℝ≥0) :
    (∫ ω, brownianCountableIntegral hB hBm hjoint hg hb hC hc T ω ^ 4 ∂P) ≤
      150 * ∫ ω, (∫ r in (0 : ℝ)..T.val, g (B r.toNNReal ω) ^ 2) ^ 2 ∂P := by
  have he (ω : Ω) : (∫ r, brownianSquareProcess (fun t ω => g (B t ω)) T (r, ω) ^ 2) =
      ∫ r in (0 : ℝ)..T.val, g (B r.toNNReal ω) ^ 2 := by
    have hi : (fun r => brownianSquareProcess (fun t ω => g (B t ω)) T (r, ω) ^ 2) =
        (Ioc (0 : ℝ) T.val).indicator (fun r => g (B r.toNNReal ω) ^ 2) := by
      funext r
      by_cases hr : r ∈ Ioc (0 : ℝ) T.val <;>
        simp only [brownianSquareProcess, indicator_apply, hr, ite_true, ite_false, one_mul, zero_mul,
          zero_pow (by norm_num : 2 ≠ 0)]
    rw [hi, integral_indicator measurableSet_Ioc]
    exact (intervalIntegral.integral_of_le (f := fun r => g (B r.toNNReal ω) ^ 2) T.coe_nonneg).symm
  simpa only [he] using (brownianCountableIntegral_fourth_energy hB hBm hjoint hg hb hC hc T).2

end TimeTraps.Probability
