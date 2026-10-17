module

public import TimeTraps.Probability.ReflectedFiniteKinkC2Formula
public import TimeTraps.Probability.ReflectedFiniteKinkC2Moments
public import TimeTraps.Probability.ReflectedInteriorOccupationMean
public import TimeTraps.Probability.ReflectedBrownianTransition

@[expose] public section

/-! A concrete single-kink test for the conditional occupation mean.
Its endpoint slopes vanish by direct calculation. The resulting actual
Itô identity contains the occupation coefficient and an original-Brownian
integral, with no boundary regulator contribution. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def reflectedInteriorOccupationTestBase (L z : ℝ) : ℝ := z - z ^ 2 / L

def reflectedInteriorOccupationTest (L a z : ℝ) : ℝ :=
  reflectedInteriorOccupationTestBase L z + |z - a|

theorem reflectedInteriorOccupationTestBase_contDiff (L : ℝ) :
    ContDiff ℝ 2 (reflectedInteriorOccupationTestBase L) := by
  unfold reflectedInteriorOccupationTestBase
  fun_prop

theorem reflectedInteriorOccupationTestBase_deriv (L : ℝ) :
    deriv (reflectedInteriorOccupationTestBase L) = fun z => 1 - 2 * z / L := by
  funext z
  have hd : HasDerivAt (reflectedInteriorOccupationTestBase L) (1 - 2 * z / L) z := by
    convert! (hasDerivAt_id z).sub (((hasDerivAt_id z).pow 2).div_const L) using 1
    simp
  exact hd.deriv

theorem reflectedInteriorOccupationTestBase_curvature (L : ℝ) :
    deriv (deriv (reflectedInteriorOccupationTestBase L)) = fun _ => -(2 / L) := by
  rw [reflectedInteriorOccupationTestBase_deriv]
  funext z
  simpa only [mul_one, zero_sub, Pi.sub_apply, id_eq] using
    ((hasDerivAt_const z (1 : ℝ)).fun_sub (((hasDerivAt_id' z).const_mul 2).div_const L)).deriv

theorem reflectedInteriorOccupationTestBase_drift (L D x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedC2ItoDrift (reflectedInteriorOccupationTestBase L) brownianDyadicPath L D x T ω =
      -(2 * T.val / L) := by
  simp only [reflectedC2ItoDrift, reflectedInteriorOccupationTestBase_curvature,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

theorem reflectedInteriorOccupationTest_continuous (L a : ℝ) :
    Continuous (reflectedInteriorOccupationTest L a) :=
  (reflectedInteriorOccupationTestBase_contDiff L).continuous.add
    (continuous_id.sub continuous_const).abs

def reflectedInteriorOccupationTestIntegrand (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) : BrownianIntegrand :=
  reflectedFiniteKinkC2Integrand (reflectedInteriorOccupationTestBase_contDiff L)
    L hL D hD (fun _ : Unit => a) (fun _ => 1) (fun _ => ha) x T

theorem reflectedInteriorOccupationTest_memLp (L : ℝ) (hL : 0 < L)
    (D x a : ℝ) (T : ℝ≥0) :
    MemLp (fun ω => reflectedInteriorOccupationTest L a
      (foldedTrajectory L D x brownianDyadicPath T ω)) 2 brownianDyadicMeasure := by
  simpa only [finiteKinkPotential, Fintype.sum_unique, one_mul, reflectedInteriorOccupationTest] using
    reflectedFiniteKinkC2_value_memLp (reflectedInteriorOccupationTestBase_contDiff L)
      L hL D x (fun _ : Unit => a) (fun _ => 1) T

theorem reflectedInteriorOccupationTest_formula (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    (fun ω => reflectedInteriorOccupationTest L a (foldedTrajectory L D x brownianDyadicPath T ω) -
      reflectedInteriorOccupationTest L a (reflectedFold L x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianStochasticIntegral (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x T) ω -
        2 * D * T.val / L +
        2 * D * reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T ω) := by
  have h0 : finiteKinkSlope (reflectedInteriorOccupationTestBase L) Finset.univ
      (fun _ : Unit => a) (fun _ => 1) 0 = 0 := by
    rw [reflectedFiniteKinkSlope_zero _ L _ _ (fun _ => ha), reflectedInteriorOccupationTestBase_deriv]
    simp only [Fintype.sum_unique, mul_zero, zero_div, sub_zero, sub_self]
  have h1 : finiteKinkSlope (reflectedInteriorOccupationTestBase L) Finset.univ
      (fun _ : Unit => a) (fun _ => 1) L = 0 := by
    rw [reflectedFiniteKinkSlope_right _ L _ _ (fun _ => ha), reflectedInteriorOccupationTestBase_deriv]
    simp only [Fintype.sum_unique, mul_div_cancel_right₀ _ (ne_of_gt hL)]
    ring
  filter_upwards [reflectedFiniteKinkC2_occupation_formula (reflectedInteriorOccupationTestBase_contDiff L)
    L hL D hD (fun _ : Unit => a) (fun _ => 1) (fun _ => ha) x T] with ω hω
  simp only [h0, h1, zero_mul, add_zero, sub_zero, reflectedInteriorOccupationTestBase_drift,
    finiteKinkPotential, Fintype.sum_unique, one_mul] at hω
  change reflectedInteriorOccupationTestBase L _ + |_-a| -
    (reflectedInteriorOccupationTestBase L _ + |_-a|) = _
  change _ = brownianStochasticIntegral (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x T) ω +
    D * -(2 * T.val / L) + 2 * D * reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T ω at hω
  linear_combination hω

end TimeTraps.Probability

end
