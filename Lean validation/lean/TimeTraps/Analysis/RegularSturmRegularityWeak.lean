module

public import TimeTraps.Analysis.RegularSturmPhysical
public import TimeTraps.Analysis.IntervalContinuousMultiplierMemLp
public import TimeTraps.Analysis.IntervalSobolevRepresentation

@[expose] public section

/-! The all-H1 weak equation determines the distributional derivative of
the physical flux p*u'. The source is q*u-sqrt(w)*f for arbitrary original
Hilbert forcing f; no pointwise regularity of f is imposed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace
open scoped Topology ContDiff

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem IntervalSeparatedBoundary.test_zero_of_tsupport_subset
    (B : IntervalSeparatedBoundary l r) {φ : ℝ → ℝ} (hs : tsupport φ ⊆ Ioo l r) :
    ∀ x ∈ B.zero_sites, φ x = 0 := by
  intro x hx
  have hout : x ∉ Ioo l r := by
    rcases B.boundary_only x hx with rfl | rfl <;> simp
  by_contra hn
  exact hout (hs (subset_closure hn))

theorem RegularSturmProblem.physicalLoad_memLp (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) :
    MemLp (fun x => f x * Real.sqrt (P.speed x)) 2 (volume.restrict (Ioo l r)) := by
  simpa only [mul_comm] using intervalContinuous_mul_memLp
    (fun x => Real.sqrt (P.speed x)) P.speed_continuous.sqrt (Lp.memLp f)

theorem RegularSturmProblem.fluxSource_memLp (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    MemLp (fun x => P.potential x * u x - f x * Real.sqrt (P.speed x)) 2
      (volume.restrict (Ioo l r)) :=
  (intervalContinuous_mul_memLp P.potential P.potential_continuous
    (hu.sobolev P.boundary.interval_pos.le).1).sub (P.physicalLoad_memLp f)

theorem RegularSturmProblem.weak_flux_derivative (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u v =
        ∫ x in l..r, f x * Real.sqrt (P.speed x) * v x)
    {a b : ℝ} (hl : l ≤ a) (hr : b ≤ r)
    (hsite : ∀ i, P.site i ∉ Ioo a b) :
    IntervalWeakDerivative (fun x => P.conductance x * deriv u x)
      (fun x => P.potential x * u x - f x * Real.sqrt (P.speed x)) a b := by
  intro φ hc _ hs
  have hs₀ : tsupport φ ⊆ Ioo l r := hs.trans (Ioo_subset_Ioo hl hr)
  have hφ : IntervalEnergy φ l r := intervalEnergy_of_continuous_derivative P.boundary.interval_pos.le
    hc.continuous.continuousOn (hc.continuous_deriv (by simp)).continuousOn
    (fun x _ => (hc.differentiable (by simp) x).hasDerivAt)
  have hzero (i : ι) : φ (P.site i) = 0 := by
    by_contra hn
    exact hsite i (hs (subset_closure hn))
  have he := hweak φ hφ (P.boundary.test_zero_of_tsupport_subset hs₀)
  simp only [regularSturmPhysicalForm, hzero, mul_zero, Finset.sum_const_zero, add_zero] at he
  have hpi : IntervalIntegrable (fun x => P.potential x * u x * φ x) volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le P.boundary.interval_pos.le).mpr
      ((intervalContinuous_mul_memLp P.potential P.potential_continuous
        (hu.sobolev P.boundary.interval_pos.le).1).integrable_mul
          (hφ.sobolev P.boundary.interval_pos.le).1)
  have hfi : IntervalIntegrable (fun x => f x * Real.sqrt (P.speed x) * φ x) volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le P.boundary.interval_pos.le).mpr
      ((P.physicalLoad_memLp f).integrable_mul (hφ.sobolev P.boundary.interval_pos.le).1)
  have hi : (∫ x in l..r, (P.potential x * u x - f x * Real.sqrt (P.speed x)) * φ x) =
      (∫ x in l..r, P.potential x * u x * φ x) -
        (∫ x in l..r, f x * Real.sqrt (P.speed x) * φ x) := by
    simp only [sub_mul]
    exact intervalIntegral.integral_sub hpi hfi
  simp only [intervalSobolev_test_integral P.boundary.interval_pos.le
    (tsupport_deriv_subset.trans hs₀),
    intervalSobolev_test_integral P.boundary.interval_pos.le hs₀] at he hi
  linarith

end TimeTraps.Analysis
