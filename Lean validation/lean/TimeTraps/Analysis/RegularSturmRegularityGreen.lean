module

public import TimeTraps.Analysis.RegularSturmRegularityPartition
public import TimeTraps.Analysis.IntervalPointRegularityGreen

@[expose] public section

/-! Actual AC integration by parts with the physical flux, and the
potential-minus-load pairing under arbitrary L2 forcing. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter

theorem IntervalFluxRegularity.green_identity {u j g p ψ : ℝ → ℝ} {l r : ℝ}
    (h : IntervalFluxRegularity u j g p l r) (hlr : l ≤ r) (hψ : IntervalEnergy ψ l r) :
    (∫ x in l..r, p x * deriv u x * deriv ψ x) =
      j r * ψ r - j l * ψ l - ∫ x in l..r, g x * ψ x := by
  rw [interval_regular_pairing_congr hlr h.flux_ae,
    h.flux_energy.absolutelyContinuous.integral_mul_deriv_eq_deriv_mul hψ.absolutelyContinuous,
    interval_regular_pairing_congr hlr h.source_ae]

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.fluxSource_pairing (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) {u ψ : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hψ : IntervalEnergy ψ l r) :
    (∫ x in l..r, (P.potential x * u x - f x * Real.sqrt (P.speed x)) * ψ x) =
      (∫ x in l..r, P.potential x * u x * ψ x) -
        (∫ x in l..r, f x * Real.sqrt (P.speed x) * ψ x) := by
  have hpi : IntervalIntegrable (fun x => P.potential x * u x * ψ x) volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le P.boundary.interval_pos.le).mpr
      ((intervalContinuous_mul_memLp P.potential P.potential_continuous
        (hu.sobolev P.boundary.interval_pos.le).1).integrable_mul
          (hψ.sobolev P.boundary.interval_pos.le).1)
  have hfi : IntervalIntegrable (fun x => f x * Real.sqrt (P.speed x) * ψ x) volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le P.boundary.interval_pos.le).mpr
      ((P.physicalLoad_memLp f).integrable_mul (hψ.sobolev P.boundary.interval_pos.le).1)
  simp only [sub_mul]
  exact intervalIntegral.integral_sub hpi hfi

end TimeTraps.Analysis
