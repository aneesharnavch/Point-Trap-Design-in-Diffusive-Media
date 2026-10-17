module

public import TimeTraps.Probability.BrownianItoDriftAdapted
public import TimeTraps.Probability.BrownianOccupationTimeBound
public import TimeTraps.Probability.BrownianFoldSlopeTimeGrid
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Bounded continuous observables require no Lipschitz assumption for
raw-past measurability of their actual time integrals. On the Brownian
continuity event, the actual dyadic time sums converge by dominated
convergence; their measurable limit supplies the raw representative. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {M : ℝ}

theorem brownianItoDriftSum_continuous_stronglyMeasurable_past
    (hBm : ∀ t, Measurable (B t)) (hg : Continuous g) (T : ℝ≥0) (n : ℕ) :
    StronglyMeasurable[brownianNaturalFiltration B hBm T] (brownianItoDriftSum B g T n) := by
  unfold brownianItoDriftSum
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  have ht : brownianDyadicGrid T n i.castSucc ≤ T := by
    simpa only [brownianDyadicGrid_last] using
      brownianDyadicGrid_monotone T n (Fin.le_last i.castSucc)
  exact (hg.comp_stronglyMeasurable
    ((brownianNaturalFiltration_stronglyAdapted B hBm _).mono
      ((brownianNaturalFiltration B hBm).mono ht))).const_mul _

theorem brownianItoDriftSum_bounded_continuous_tendsto (hg : Continuous g)
    (hb : ∀ z, |g z| ≤ M) (T : ℝ≥0) (ω : Ω)
    (hpath : Continuous (fun t => B t ω)) :
    Tendsto (fun n => brownianItoDriftSum B g T n ω) atTop (𝓝 (brownianItoDrift B g T ω)) := by
  have hd := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc (0 : ℝ) T.val))
    (F := fun n r => brownianLipschitzStepProcess B g T n (r, ω))
    (f := fun r => g (B r.toNNReal ω)) (fun _ => M)
    (fun n => (brownianItoDriftSum_step_integrable B g T n ω).aestronglyMeasurable.restrict)
    (integrable_const M) (fun n => ?_) ?_
  · have he (n : ℕ) : (∫ r in Ioc (0 : ℝ) T.val,
        brownianLipschitzStepProcess B g T n (r, ω)) = brownianItoDriftSum B g T n ω :=
      (intervalIntegral.integral_of_le T.coe_nonneg).symm.trans
        (brownianItoDriftSum_step_integral B g T n ω)
    have hf : brownianItoDrift B g T ω = ∫ r in Ioc (0 : ℝ) T.val, g (B r.toNNReal ω) :=
      intervalIntegral.integral_of_le T.coe_nonneg
    rw [hf]
    simpa only [he] using hd
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    obtain ⟨i, hi⟩ := brownianDyadicGrid_cell T n hr
    rw [brownianLipschitzStepProcess, brownianSquareStepProcess_cell _ T n ω i hi, Real.norm_eq_abs]
    exact hb _
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have ht := brownianSquareStepProcess_tendsto_at (fun t ω => g (B t ω)) T (r, ω)
      (fun _ => (hg.comp hpath).continuousAt)
    simpa only [brownianLipschitzStepProcess, brownianSquareProcess, Set.indicator_of_mem hr, one_mul] using ht

theorem brownianItoDrift_continuous_aestronglyMeasurable_past (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : Continuous g) (hb : ∀ z, |g z| ≤ M) (T : ℝ≥0) :
    AEStronglyMeasurable[brownianNaturalFiltration B hBm T] (brownianItoDrift B g T) P := by
  let V (ω : Ω) : ℝ := limUnder atTop (fun n => brownianItoDriftSum B g T n ω)
  refine ⟨V, ?_, ?_⟩
  · have hseq := fun n => brownianItoDriftSum_continuous_stronglyMeasurable_past hBm hg T n
    let : MeasurableSpace Ω := brownianNaturalFiltration B hBm T
    exact StronglyMeasurable.limUnder hseq
  · filter_upwards [hB.cont] with ω hω
    exact (brownianItoDriftSum_bounded_continuous_tendsto hg hb T ω hω).limUnder_eq.symm

theorem brownianItoDrift_continuous_condExp_past (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : Continuous g) (hb : ∀ z, |g z| ≤ M)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) {T s : ℝ≥0} (hTs : T ≤ s) :
    P[brownianItoDrift B g T | brownianNaturalFiltration B hBm s] =ᵐ[P] brownianItoDrift B g T := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  exact condExp_of_aestronglyMeasurable' ((brownianNaturalFiltration B hBm).le s)
    ((brownianItoDrift_continuous_aestronglyMeasurable_past hB hBm hg hb T).mono
      ((brownianNaturalFiltration B hBm).mono hTs))
    ((brownianItoDrift_bounded_memLp hg.measurable hjoint hb T).integrable (by norm_num))

end TimeTraps.Probability
