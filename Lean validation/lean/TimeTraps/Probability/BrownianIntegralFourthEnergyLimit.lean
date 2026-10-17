module

public import TimeTraps.Probability.BrownianIntegralFourthTimeEnergy
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-! The squared accumulated energies of uniformly bounded dyadic samples
converge in expectation. Product-almost-everywhere convergence is exchanged
by measurable Fubini before applying dominated convergence in time and sample. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {H : ℝ≥0 → Ω → ℝ} {M : ℝ≥0}

theorem brownian_fourth_cutoff_square (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (p : ℝ × Ω) :
    brownianSquareProcess H T p ^ 2 = brownianSquareProcess (fun t ω => H t ω ^ 2) T p := by
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val <;>
    simp only [brownianSquareProcess, indicator_apply, hp, ite_true, ite_false, one_mul, zero_mul, zero_pow (by norm_num : 2 ≠ 0)]

theorem brownian_fourth_step_energy_square_tendsto [IsFiniteMeasure P]
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0)
    (hlim : ∀ᵐ p ∂volume.prod P, Tendsto (fun n => brownianSquareStepProcess H T n p) atTop
      (𝓝 (brownianSquareProcess H T p))) :
    Tendsto (fun n => ∫ ω, (∫ r, brownianSquareStepProcess H T n (r, ω) ^ 2) ^ 2 ∂P) atTop
      (𝓝 (∫ ω, (∫ r, brownianSquareProcess H T (r, ω) ^ 2) ^ 2 ∂P)) := by
  have hH (t : ℝ≥0) : Measurable (H t) := hjoint.comp (measurable_const.prodMk measurable_id)
  have hm (n : ℕ) := brownianAdaptedContinuous_step_measurable hH T n
  have hg := brownianSquareProcess_measurable hjoint T
  have hmconv : MeasurableSet {p : ℝ × Ω | Tendsto (fun n => brownianSquareStepProcess H T n p) atTop
      (𝓝 (brownianSquareProcess H T p))} := measurableSet_tendsto_fun hm hg
  have hAE : ∀ᵐ ω ∂P, ∀ᵐ r ∂volume, Tendsto (fun n => brownianSquareStepProcess H T n (r, ω)) atTop
      (𝓝 (brownianSquareProcess H T (r, ω))) :=
    (Measure.ae_ae_comm hmconv).mp (Measure.ae_ae_of_ae_prod hlim)
  have hb2 (t : ℝ≥0) (ω : Ω) : |H t ω ^ 2| ≤ (M ^ 2).val := by
    change |H t ω ^ 2| ≤ M.val ^ 2
    rw [abs_sq]
    have hr := hb t ω
    have hM := M.coe_nonneg
    nlinarith [sq_abs (H t ω), abs_nonneg (H t ω)]
  have hinner : ∀ᵐ ω ∂P, Tendsto (fun n => ∫ r, brownianSquareStepProcess H T n (r, ω) ^ 2) atTop
      (𝓝 (∫ r, brownianSquareProcess H T (r, ω) ^ 2)) := by
    filter_upwards [hAE] with ω hω
    apply tendsto_integral_of_dominated_convergence (fun r => M.val ^ 2 * brownianIntervalIndicator 0 T r)
      (fun n => ((hm n).comp (measurable_id.prodMk (measurable_const (a := ω)))).pow_const 2 |>.aestronglyMeasurable)
      ((brownianIntervalIndicator_integrable 0 T).const_mul (M.val ^ 2))
    · intro n
      filter_upwards [] with r
      change ‖brownianSquareStepProcess H T n (r, ω) ^ 2‖ ≤ M.val ^ 2 * brownianIntervalIndicator 0 T r
      rw [Real.norm_eq_abs, brownian_fourth_step_square]
      exact brownianAdaptedContinuous_step_bound hb2 T n (r, ω)
    · exact hω.mono (fun _ hr => hr.pow 2)
  have hFbound (n : ℕ) (ω : Ω) :
      0 ≤ (∫ r, brownianSquareStepProcess H T n (r, ω) ^ 2) ∧
      (∫ r, brownianSquareStepProcess H T n (r, ω) ^ 2) ≤ T.val * M.val ^ 2 :=
    (brownian_fourth_cutoff_energy_bound
      ((hm n).comp (measurable_id.prodMk (measurable_const (a := ω)))) M T
      (fun r => brownianAdaptedContinuous_step_bound hb T n (r, ω))).2
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (T.val * M.val ^ 2) ^ 2)
    (fun n => (((hm n).pow_const 2).stronglyMeasurable.integral_prod_left').measurable.pow_const 2 |>.aestronglyMeasurable)
    (integrable_const _)
  · intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_sq]
    exact (sq_le_sq₀ (hFbound n ω).1 (mul_nonneg T.coe_nonneg (sq_nonneg _))).mpr (hFbound n ω).2
  · exact hinner.mono (fun _ hω => hω.pow 2)

end TimeTraps.Probability
