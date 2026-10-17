module

public import TimeTraps.Analysis.IntervalEnergyGluing
public import TimeTraps.Analysis.IntervalPointRegularityPartition

@[expose] public section

/-! Closed-piece H1 certificates glue along a finite ordered partition.
Each certificate uses the same actual state, so continuity and matching
endpoint values are retained rather than assumed as separate data. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

theorem intervalEnergy_of_finite_chain {n : ℕ} (q : Fin (n + 2) → ℝ)
    (hq : Monotone q) {u : ℝ → ℝ}
    (hu : ∀ e : Fin (n + 1), IntervalEnergy u (q e.castSucc) (q e.succ)) :
    IntervalEnergy u (q 0) (q (Fin.last (n + 1))) := by
  induction n with
  | zero => simpa using hu 0
  | succ n ih =>
    have hl := ih (fun v : Fin (n + 2) => q v.castSucc)
      (hq.comp Fin.strictMono_castSucc.monotone) (fun e => by
        simpa only [Fin.succ_castSucc] using hu e.castSucc)
    have hr := hu (Fin.last (n + 1))
    have he := hl.trans hr (hq (Fin.zero_le _)) (hq (Fin.castSucc_le_succ _))
    simpa only [Fin.castSucc_zero, Fin.succ_last] using he

theorem UnitPointPartition.energy_of_piecewise {ι : Type*} [Fintype ι]
    {P : UnitPointProblem ι} {n : ℕ} (Q : UnitPointPartition P n) {u : ℝ → ℝ}
    (hu : ∀ e : Fin (n + 1), IntervalEnergy u (Q.point e.castSucc) (Q.point e.succ)) :
    IntervalEnergy u 0 1 := by
  simpa only [Q.left_eq, Q.right_eq] using
    intervalEnergy_of_finite_chain Q.point Q.strictMono.monotone hu

theorem UnitPointPartition.energy_of_slopes {ι : Type*} [Fintype ι]
    {P : UnitPointProblem ι} {n : ℕ} (Q : UnitPointPartition P n)
    {u g : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ}
    (hj : ∀ e, IntervalSlopeRegularity u (j e) g (Q.point e.castSucc) (Q.point e.succ)) :
    IntervalEnergy u 0 1 := Q.energy_of_piecewise (fun e => (hj e).state_energy)

end TimeTraps.Analysis
