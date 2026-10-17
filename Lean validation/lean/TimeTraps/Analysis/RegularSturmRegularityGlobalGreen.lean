module

public import TimeTraps.Analysis.RegularSturmRegularityGreen

@[expose] public section

/-! The full variable-coefficient Green identity follows by summing
the derived physical flux identities over all contact-free cells. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {l r : ℝ} {P : RegularSturmProblem ι l r} {n : ℕ}

theorem RegularSturmPartition.global_green (Q : RegularSturmPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalFluxRegularity u (j e)
      (fun x => P.potential x * u x - f x * Real.sqrt (P.speed x)) P.conductance
      (Q.point e.castSucc) (Q.point e.succ))
    (ψ : ℝ → ℝ) (hψ : IntervalEnergy ψ l r) :
    (∫ x in l..r, P.conductance x * deriv u x * deriv ψ x) +
      (∫ x in l..r, P.potential x * u x * ψ x) =
      (∫ x in l..r, f x * Real.sqrt (P.speed x) * ψ x) +
        ∑ e, (j e (Q.point e.succ) * ψ (Q.point e.succ) -
          j e (Q.point e.castSucc) * ψ (Q.point e.castSucc)) := by
  have hdi : IntervalIntegrable (fun x => P.conductance x * deriv u x * deriv ψ x) volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le P.boundary.interval_pos.le).mpr
      ((hu.weighted_derivative_memLp P.boundary.interval_pos.le P.conductance P.conductance_continuous).integrable_mul (hψ.derivative_memLp.mono_measure (by
          rw [uIoc_of_le P.boundary.interval_pos.le]
          exact Measure.restrict_mono_set volume Ioo_subset_Ioc_self)))
  have hgi : IntervalIntegrable
      (fun x => (P.potential x * u x - f x * Real.sqrt (P.speed x)) * ψ x) volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le P.boundary.interval_pos.le).mpr
      ((P.fluxSource_memLp f hu).integrable_mul (hψ.sobolev P.boundary.interval_pos.le).1)
  have hd := piecewise_integral_sum Q.point Q.strictMono.monotone
    (fun x => P.conductance x * deriv u x * deriv ψ x)
    (by simpa only [Q.left_eq, Q.right_eq] using hdi)
  have hg := piecewise_integral_sum Q.point Q.strictMono.monotone
    (fun x => (P.potential x * u x - f x * Real.sqrt (P.speed x)) * ψ x)
    (by simpa only [Q.left_eq, Q.right_eq] using hgi)
  simp only [Q.left_eq, Q.right_eq] at hd hg
  have he (e : Fin (n + 1)) := (hj e).green_identity
    (Q.strictMono Fin.castSucc_lt_succ).le (hψ.mono (show
      uIcc (Q.point e.castSucc) (Q.point e.succ) ⊆ uIcc l r by
        rw [uIcc_of_le (Q.strictMono Fin.castSucc_lt_succ).le, uIcc_of_le P.boundary.interval_pos.le]
        exact Icc_subset_Icc (Q.point_mem e.castSucc).1 (Q.point_mem e.succ).2))
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun e _ => he e)
  rw [Finset.sum_sub_distrib, hd, hg, P.fluxSource_pairing f hu hψ] at hs
  linarith

end TimeTraps.Analysis
