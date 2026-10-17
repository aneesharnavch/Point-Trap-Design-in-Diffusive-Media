module

public import TimeTraps.Analysis.SignedPeriodicPointHeat
public import TimeTraps.Analysis.SignedPeriodicPointRegularityDomain

@[expose] public section

/-! The actual heat generator has the full piecewise H2 domain. At each
positive time, arbitrary L2 initial data have AC/L2 slope representatives
with spatial second derivative equal to the time derivative divided by D.
The finite partition is derived. Endpoint values match and the single seam
flux law combines both endpoint contact sums, with signed interior jumps. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedPeriodicPointProblem.heat_generator_iff_piecewise
    (P : SignedPeriodicPointProblem ι l r) (u f : IntervalSobolevL2 l r) :
    HasDerivWithinAt (P.heatCurve u) (-f) (Ici 0) 0 ↔
      ∃ (n : ℕ) (Q : SignedPeriodicPointPartition P n) (U : ℝ → ℝ)
        (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo l r)] U ∧
        (∀ e, IntervalSlopeRegularity U (j e) (fun y => -f y / P.diffusivity)
          (Q.point e.castSucc) (Q.point e.succ)) ∧ SignedPeriodicPointTransmission Q U j :=
  (P.heat_generator_iff_graph u f).trans (P.operator_graph_iff_exists_partition u f)

theorem SignedPeriodicPointProblem.heat_strong_of_pos
    (P : SignedPeriodicPointProblem ι l r) (x : IntervalSobolevL2 l r)
    {t : ℝ} (ht : 0 < t) :
    ∃ (n : ℕ) (Q : SignedPeriodicPointPartition P n) (U : ℝ → ℝ)
      (j : Fin (n + 1) → ℝ → ℝ),
      P.heatCurve x t =ᵐ[volume.restrict (Ioo l r)] U ∧
      (∀ e, IntervalSlopeRegularity U (j e)
        (fun y => (deriv (P.heatCurve x) t) y / P.diffusivity)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ SignedPeriodicPointTransmission Q U j := by
  obtain ⟨n, Q, U, j, hU, hj, hb⟩ :=
    (P.operator_graph_iff_exists_partition _ _).mp (P.heat_deriv_graph_of_pos x ht)
  refine ⟨n, Q, U, j, hU, ?_, hb⟩
  intro e
  refine ⟨(hj e).state_energy, (hj e).slope_energy, (hj e).slope_ae, ?_⟩
  have hn := (Lp.coeFn_neg (deriv (P.heatCurve x) t)).filter_mono
    (ae_mono (Measure.restrict_mono_set volume
      (Ioo_subset_Ioo (Q.point_mem e.castSucc).1 (Q.point_mem e.succ).2)))
  filter_upwards [(hj e).second_ae, hn] with y hy hneg
  change (-deriv (P.heatCurve x) t) y = -(deriv (P.heatCurve x) t) y at hneg
  change deriv (j e) y = -(-deriv (P.heatCurve x) t) y / P.diffusivity at hy
  rw [hneg, neg_neg] at hy
  exact hy

end TimeTraps.Analysis
