module

public import TimeTraps.Probability.ReflectedRobinWeakKink
public import TimeTraps.Probability.ReflectedRobinRunningCostData
public import TimeTraps.Probability.ReflectedRobinKilling

@[expose] public section

/-! Every solution of the original full H1 Robin equation satisfies the
actual finite-time killed formula and its expectation identity. The
source is continuous only on the physical interval and may have either
sign. All required finite-time integrability is proved. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {L D : ℝ} {a κ : ι → ℝ} {β₀ βL : ℝ} {g u : ℝ → ℝ}

def reflectedRobinWeakIntegrand (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (hg : ContinuousOn g (Icc 0 L))
    (x : ℝ) (T : ℝ≥0) : BrownianIntegrand :=
  reflectedAtomicSurvivalMultiplier L hL D hD x (reflectedRobinSite L a)
    (reflectedRobinStrength κ β₀ βL) (reflectedRobinStrength_nonneg hκ hβ₀ hβL)
    (reflectedFiniteKinkC2Integrand (hu.kinkBase_contDiff hL hg) L hL D hD a hu.kinkCoefficient ha x T)

theorem ReflectedRobinWeakEquation.actual_finite (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (hg : ContinuousOn g (Icc 0 L)) (x : ℝ) (T : ℝ≥0) :
    (fun ω => reflectedRobinSurvival L D x a κ β₀ βL T ω *
      u (foldedTrajectory L D x brownianDyadicPath T ω) - u (reflectedFold L x))
      =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedRobinWeakIntegrand hu hL hD ha hκ hβ₀ hβL hg x T) ω -
        ∫ r in (0 : ℝ)..T.val, reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω *
          g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) := by
  filter_upwards [reflectedRobinC2_running_cost_formula (hu.kinkBase_contDiff hL hg)
    L hL D hD a hu.kinkCoefficient κ ha hκ β₀ βL hβ₀ hβL x T
    (hu.kinkPotential_robin hL hD ha hg).1 (hu.kinkPotential_robin hL hD ha hg).2
    (hu.kinkPotential_reaction hL hD ha hg) g (fun _ hz => hu.kinkBase_source hL hD hg hz)] with ω hf
  have hv := hu.kinkPotential_eq hL hD hg (foldedTrajectory_mem L hL D x brownianDyadicPath T ω)
  have hx := hu.kinkPotential_eq hL hD hg (reflectedFold_mem L hL x)
  change finiteKinkPotential (hu.kinkBase hL hg) Finset.univ a hu.kinkCoefficient _ = _ at hv hx
  rw [hv, hx] at hf
  exact hf

theorem ReflectedRobinWeakEquation.actual_state_memLp (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (x : ℝ) (T : ℝ≥0) :
    MemLp (fun ω => reflectedRobinSurvival L D x a κ β₀ βL T ω *
      u (foldedTrajectory L D x brownianDyadicPath T ω)) 2 brownianDyadicMeasure := by
  simp only [reflectedRobinSurvival_eq_atomic L hD]
  apply reflectedRobinRunningCost_memLp L hL D hD _ _ (reflectedRobinStrength_nonneg hκ hβ₀ hβL) _ x T
  simpa only [uIcc_of_le hL.le] using hu.energy.continuousOn

theorem ReflectedRobinWeakEquation.actual_expected_finite (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (hg : ContinuousOn g (Icc 0 L)) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..T.val, reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω *
      g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) ∂brownianDyadicMeasure) =
      u (reflectedFold L x) - ∫ ω, reflectedRobinSurvival L D x a κ β₀ βL T ω *
        u (foldedTrajectory L D x brownianDyadicPath T ω) ∂brownianDyadicMeasure := by
  have hV := (hu.actual_state_memLp hL hD hκ hβ₀ hβL x T).integrable (by norm_num)
  have hI := (Lp.memLp (brownianIntegral brownianDyadicPath_isPreBrownianReal
    (reflectedRobinWeakIntegrand hu hL hD ha hκ hβ₀ hβL hg x T))).integrable (by norm_num)
  have hA : Integrable (fun ω => ∫ r in (0 : ℝ)..T.val,
      reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω *
        g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) brownianDyadicMeasure := by
    simp only [reflectedRobinSurvival_eq_atomic L hD]
    exact reflectedRobinRunningCost_time_integral_integrable L hL D hD _ _
      (reflectedRobinStrength_nonneg hκ hβ₀ hβL) hg x T
  have he := integral_congr_ae (hu.actual_finite hL hD ha hκ hβ₀ hβL hg x T)
  rw [integral_sub hV (integrable_const _), integral_sub hI hA,
    brownianIntegral_mean brownianDyadicPath_isPreBrownianReal] at he
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, zero_sub] at he
  linarith

theorem ReflectedRobinWeakEquation.actual_expected_time_finite (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (hg : ContinuousOn g (Icc 0 L)) (x : ℝ) (T : ℝ≥0) :
    (∫ r in (0 : ℝ)..T.val, ∫ ω, reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω *
      g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) ∂brownianDyadicMeasure) =
      u (reflectedFold L x) - ∫ ω, reflectedRobinSurvival L D x a κ β₀ βL T ω *
        u (foldedTrajectory L D x brownianDyadicPath T ω) ∂brownianDyadicMeasure := by
  have he := hu.actual_expected_finite hL hD ha hκ hβ₀ hβL hg x T
  simp only [reflectedRobinSurvival_eq_atomic L hD] at he ⊢
  exact (reflectedRobinRunningCost_mean_time_integral L hL D hD
    (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
    (reflectedRobinStrength_nonneg hκ hβ₀ hβL) hg x T).symm.trans he

end TimeTraps.Probability

end
