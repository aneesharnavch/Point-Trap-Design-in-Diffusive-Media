module

public import TimeTraps.Probability.BrownianFoldSlopeTimeGrid

@[expose] public section

/-! Bounded time-dependent processes and their actual left dyadic
samples. These analytic facts require no stochastic-integrand membership.
Almost-sure continuous paths imply product-almost-everywhere convergence,
with the zero horizon included by the actual interval cutoff. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {H : ℝ≥0 → Ω → ℝ} {M : ℝ≥0}

theorem brownianAdaptedContinuous_cutoff_bound
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (p : ℝ × Ω) :
    |brownianSquareProcess H T p| ≤ M.val * brownianIntervalIndicator 0 T p.1 := by
  change |(Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * H p.1.toNNReal p.2| ≤
    M.val * (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · simpa only [Set.indicator_of_mem hp, one_mul, mul_one] using hb p.1.toNNReal p.2
  · simp only [Set.indicator_of_notMem hp, zero_mul, mul_zero, abs_zero, le_refl]

theorem brownianAdaptedContinuous_cutoff_memLp [IsFiniteMeasure P]
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) :
    MemLp (brownianSquareProcess H T) 2 ((volume : Measure ℝ).prod P) := by
  apply (brownianElementaryProcess_memLp (P := P) 0 T measurable_const
    (memLp_const M.val)).mono' (brownianSquareProcess_measurable hjoint T).aestronglyMeasurable
  filter_upwards [] with p
  simpa only [brownianElementaryProcess, Real.norm_eq_abs, mul_comm] using
    brownianAdaptedContinuous_cutoff_bound hb T p

theorem brownianAdaptedContinuous_step_measurable (hH : ∀ t, Measurable (H t))
    (T : ℝ≥0) (n : ℕ) : Measurable (brownianSquareStepProcess H T n) := by
  unfold brownianSquareStepProcess
  apply Finset.measurable_sum
  intro i _
  exact brownianElementaryProcess_measurable _ _ (hH _)

theorem brownianAdaptedContinuous_step_bound
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) :
    |brownianSquareStepProcess H T n p| ≤ M.val * brownianIntervalIndicator 0 T p.1 := by
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · obtain ⟨i, hi⟩ := brownianDyadicGrid_cell T n hp
    rw [brownianSquareStepProcess_cell H T n p.2 i hi]
    change |H (brownianDyadicGrid T n i.castSucc) p.2| ≤
      M.val * (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
    simpa only [Set.indicator_of_mem hp, mul_one] using
      hb (brownianDyadicGrid T n i.castSucc) p.2
  · rw [brownianSquareStepProcess_outside H T n p.2 hp]
    change |(0 : ℝ)| ≤ M.val * (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
    simp only [Set.indicator_of_notMem hp, abs_zero, mul_zero, le_refl]

theorem brownianAdaptedContinuous_step_tendsto_ae [IsFiniteMeasure P]
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => brownianSquareStepProcess H T n p) atTop
        (𝓝 (brownianSquareProcess H T p)) := by
  have hc : ∀ᵐ p ∂(volume : Measure ℝ).prod P, Continuous (fun t => H t p.2) :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := P)).ae hcont
  filter_upwards [hc] with p hp
  exact brownianSquareStepProcess_tendsto_at H T p (fun _ => hp.continuousAt)

end TimeTraps.Probability
