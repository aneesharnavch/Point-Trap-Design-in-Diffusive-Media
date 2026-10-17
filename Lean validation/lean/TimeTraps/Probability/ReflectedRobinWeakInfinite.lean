module

public import TimeTraps.Probability.ReflectedRobinRunningCostInfinite

@[expose] public section

/-! The positive-source Robin weak equation equals the actual whole-time
expected cost, including endpoint-only reaction families. Finiteness and
decay follow from the weak solution, rather than being assumptions on
the stochastic process. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {L D : ℝ} {a κ : ι → ℝ} {β₀ βL : ℝ} {g u : ℝ → ℝ}

theorem ReflectedRobinWeakEquation.actual_source_joint_integrable
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (hg : ContinuousOn g (Icc 0 L))
    (hupos : ∀ z ∈ Icc 0 L, 0 ≤ u z) {c : ℝ} (hc : 0 < c)
    (hcg : ∀ z ∈ Icc 0 L, c ≤ g z) (x : ℝ) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => reflectedAtomicWeightedValue g L D x
      (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL) p.1.toNNReal p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod brownianDyadicMeasure) :=
  reflectedRobinRunningCost_joint_integrable_of_survival L hL D hD
    (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
    (reflectedRobinStrength_nonneg hκ hβ₀ hβL) hg x
    (hu.actual_survival_integrable hL hD ha hκ hβ₀ hβL hg hupos hc hcg x)

theorem ReflectedRobinWeakEquation.actual_expected_time_infinite
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (hg : ContinuousOn g (Icc 0 L))
    (hupos : ∀ z ∈ Icc 0 L, 0 ≤ u z) {c : ℝ} (hc : 0 < c)
    (hcg : ∀ z ∈ Icc 0 L, c ≤ g z) (x : ℝ) :
    (∫ r in Ioi (0 : ℝ), reflectedAtomicValueExpectation g L D x
      (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL) r.toNNReal) = u (reflectedFold L x) := by
  have hs := hu.actual_survival_tendsto hL hD ha hκ hβ₀ hβL hg hupos hc hcg x
  have huc : ContinuousOn u (Icc 0 L) := by
    simpa only [uIcc_of_le hL.le] using hu.energy.continuousOn
  have hu0 := reflectedRobinRunningCost_expectation_tendsto_of_survival L hL D hD
    (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
    (reflectedRobinStrength_nonneg hκ hβ₀ hβL) huc x hs
  have hfin (T : ℝ≥0) : (∫ r in (0 : ℝ)..T.val, reflectedAtomicValueExpectation g L D x
      (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL) r.toNNReal) =
      u (reflectedFold L x) - reflectedAtomicValueExpectation u L D x
        (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL) T := by
    simpa only [reflectedRobinSurvival_eq_atomic L hD, reflectedAtomicValueExpectation,
      reflectedAtomicWeightedValue] using
      hu.actual_expected_time_finite hL hD ha hκ hβ₀ hβL hg x T
  have ht : Tendsto (fun T : ℝ≥0 => ∫ r in (0 : ℝ)..T.val, reflectedAtomicValueExpectation g L D x
      (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL) r.toNNReal)
      atTop (𝓝 (u (reflectedFold L x))) := by
    simpa only [hfin, sub_zero] using hu0.const_sub (u (reflectedFold L x))
  exact tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0
    (hu.actual_source_joint_integrable hL hD ha hκ hβ₀ hβL hg hupos hc hcg x).integral_prod_left
    (NNReal.tendsto_coe_atTop.mpr tendsto_id)) ht

theorem ReflectedRobinWeakEquation.actual_expected_infinite
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (hg : ContinuousOn g (Icc 0 L))
    (hupos : ∀ z ∈ Icc 0 L, 0 ≤ u z) {c : ℝ} (hc : 0 < c)
    (hcg : ∀ z ∈ Icc 0 L, c ≤ g z) (x : ℝ) :
    (∫ ω, (∫ r in Ioi (0 : ℝ), reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω *
      g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) ∂brownianDyadicMeasure) =
      u (reflectedFold L x) := by
  simp only [reflectedRobinSurvival_eq_atomic L hD]
  exact (integral_integral_swap
    (hu.actual_source_joint_integrable hL hD ha hκ hβ₀ hβL hg hupos hc hcg x)).symm.trans
    (hu.actual_expected_time_infinite hL hD ha hκ hβ₀ hβL hg hupos hc hcg x)

end TimeTraps.Probability
