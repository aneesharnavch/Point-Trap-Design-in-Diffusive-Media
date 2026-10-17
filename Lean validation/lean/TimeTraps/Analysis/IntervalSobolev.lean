module

public import TimeTraps.Analysis.IntervalEnergy
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! The distributional presentation of interval H1, independently defined
by square integrability and all smooth compactly supported tests. This file
proves the direction from the existing absolutely continuous energy model.
No absolute continuity or pointwise derivative is built into IntervalSobolev. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Function
open scoped Topology ContDiff Distributions

def IntervalWeakDerivative (u g : ℝ → ℝ) (l r : ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo l r →
    (∫ x, u x * deriv φ x) = -(∫ x, g x * φ x)

def IntervalSobolev (u : ℝ → ℝ) (l r : ℝ) : Prop :=
  MemLp u 2 (volume.restrict (Ioo l r)) ∧
    ∃ g : ℝ → ℝ, MemLp g 2 (volume.restrict (Ioo l r)) ∧ IntervalWeakDerivative u g l r

/-- A compact interior test has the same whole-line and interval pairing. -/
theorem intervalSobolev_test_integral {f φ : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hφ : tsupport φ ⊆ Ioo l r) :
    (∫ x in l..r, f x * φ x) = ∫ x, f x * φ x := by
  rw [intervalIntegral.integral_of_le hlr]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : φ x = 0 := by
    by_contra hn
    have hm : x ∈ Ioo l r := hφ (subset_closure hn)
    exact hx ⟨hm.1, hm.2.le⟩
  rw [hz, mul_zero]

/-- The unbundled tests are exactly Mathlib's smooth test functions on the
open interval, not a restricted finite family of probes. -/
theorem intervalWeakDerivative_iff_testFunction (u g : ℝ → ℝ) (l r : ℝ) :
    IntervalWeakDerivative u g l r ↔
      ∀ φ : 𝓓(⟨Ioo l r, isOpen_Ioo⟩, ℝ),
        (∫ x, u x * deriv φ x) = -(∫ x, g x * φ x) := by
  constructor
  · intro h φ
    exact h φ φ.contDiff φ.hasCompactSupport φ.tsupport_subset
  · intro h φ hc hk hs
    exact h ⟨φ, hc, hk, hs⟩

/-- Integration by parts proves the actual a.e. derivative is the
distributional weak derivative of every energy state. -/
theorem IntervalEnergy.weakDerivative {u : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l ≤ r) :
    IntervalWeakDerivative u (deriv u) l r := by
  intro φ hc _ hs
  have hφ : IntervalEnergy φ l r := intervalEnergy_of_continuous_derivative hlr
    hc.continuous.continuousOn (hc.continuous_deriv (by simp)).continuousOn
    (fun x _ => (hc.differentiable (by simp) x).hasDerivAt)
  have hl : φ l = 0 := by
    by_contra hn
    exact (lt_irrefl l) (hs (subset_closure hn)).1
  have hr : φ r = 0 := by
    by_contra hn
    exact (lt_irrefl r) (hs (subset_closure hn)).2
  have hi := hu.absolutelyContinuous.integral_mul_deriv_eq_deriv_mul hφ.absolutelyContinuous
  rw [hl, hr, mul_zero, mul_zero, sub_self, zero_sub] at hi
  rw [intervalSobolev_test_integral hlr (tsupport_deriv_subset.trans hs),
    intervalSobolev_test_integral hlr hs] at hi
  exact hi

/-- Full interval energy membership implies the independent weak-derivative
H1 definition, including L2 membership of both the state and derivative. -/
theorem IntervalEnergy.sobolev {u : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l ≤ r) : IntervalSobolev u l r := by
  have hm : volume.restrict (Ioo l r) ≤ volume.restrict (uIoc l r) := by
    rw [uIoc_of_le hlr]
    exact Measure.restrict_mono_set volume Ioo_subset_Ioc_self
  have hs : MemLp u 2 (volume.restrict (uIoc l r)) :=
    (memLp_two_iff_integrable_sq
      (intervalIntegrable_iff.mp hu.continuousOn.intervalIntegrable).aestronglyMeasurable).mpr
        (intervalIntegrable_iff.mp hu.state_square_integrable)
  exact ⟨hs.mono_measure hm, deriv u, hu.derivative_memLp.mono_measure hm,
    hu.weakDerivative hlr⟩

end TimeTraps.Analysis
