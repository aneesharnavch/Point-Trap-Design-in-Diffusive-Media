module

public import TimeTraps.Analysis.RegularSturmRegularityGlobalGreen

@[expose] public section

/-! Full H1 node tests give the actual physical flux balance at every
contact and every unselected endpoint. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {l r : ℝ} {P : RegularSturmProblem ι l r} {n : ℕ}

theorem RegularSturmPartition.weak_flux_balance (Q : RegularSturmPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r →
      (∀ x ∈ P.boundary.zero_sites, ψ x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u ψ = ∫ x in l..r, f x * Real.sqrt (P.speed x) * ψ x)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalFluxRegularity u (j e) (fun x => P.potential x * u x - f x * Real.sqrt (P.speed x)) P.conductance
      (Q.point e.castSucc) (Q.point e.succ))
    (ψ : ℝ → ℝ) (hψ : IntervalEnergy ψ l r)
    (hψz : ∀ x ∈ P.boundary.zero_sites, ψ x = 0) :
    (∑ e, (j e (Q.point e.succ) * ψ (Q.point e.succ) -
      j e (Q.point e.castSucc) * ψ (Q.point e.castSucc))) +
      ∑ i, P.strength i * u (P.site i) * ψ (P.site i) = 0 := by
  have hg := Q.global_green f hu j hj ψ hψ
  have hw := hweak ψ hψ hψz
  unfold regularSturmPhysicalForm at hw
  linarith

theorem RegularSturmPartition.node_balance (Q : RegularSturmPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r →
      (∀ x ∈ P.boundary.zero_sites, ψ x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u ψ = ∫ x in l..r, f x * Real.sqrt (P.speed x) * ψ x)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalFluxRegularity u (j e) (fun x => P.potential x * u x - f x * Real.sqrt (P.speed x)) P.conductance
      (Q.point e.castSucc) (Q.point e.succ)) (v : Fin (n + 2))
    (hv : Q.point v ∉ P.boundary.zero_sites) :
    (∑ e : Fin (n + 1),
      ((if e.succ = v then j e (Q.point v) else 0) -
       (if e.castSucc = v then j e (Q.point v) else 0))) +
      Q.nodeStrength v * u (Q.point v) = 0 := by
  have hb := Q.weak_flux_balance f hu hweak j hj (intervalNodeTest Q.point v)
    (intervalNodeTest_energy_interval Q.point v P.boundary.interval_pos.le) (Q.nodeTest_zero v hv)
  rw [Q.nodeTest_reaction] at hb
  have he : (∑ e : Fin (n + 1),
      (j e (Q.point e.succ) * intervalNodeTest Q.point v (Q.point e.succ) -
       j e (Q.point e.castSucc) * intervalNodeTest Q.point v (Q.point e.castSucc))) =
      ∑ e : Fin (n + 1),
      ((if e.succ = v then j e (Q.point v) else 0) -
       (if e.castSucc = v then j e (Q.point v) else 0)) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [intervalNodeTest_node Q.point Q.strictMono.injective,
      intervalNodeTest_node Q.point Q.strictMono.injective]
    by_cases hs : e.succ = v <;> by_cases hc : e.castSucc = v <;> simp [hs, hc]
  rwa [he] at hb

end TimeTraps.Analysis
