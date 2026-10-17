module

public import TimeTraps.Analysis.IntervalPointRegularityGreen
public import TimeTraps.Analysis.IntervalPeriodicRegularityPartition

@[expose] public section

/-! Sum the actual AC/L2 Green identities over the partition. The complete
periodic weak equation then determines internal node balances and one seam balance. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {P : PeriodicPointProblem ι l r} {n : ℕ}

theorem PeriodicPointPartition.global_green (Q : PeriodicPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ))
    (ψ : ℝ → ℝ) (hψ : IntervalEnergy ψ l r) :
    P.diffusivity * (∫ x in l..r, deriv u x * deriv ψ x) =
      (∫ x in l..r, f x * ψ x) +
      ∑ e, (P.diffusivity * j e (Q.point e.succ) * ψ (Q.point e.succ) -
        P.diffusivity * j e (Q.point e.castSucc) * ψ (Q.point e.castSucc)) := by
  have hdi : IntervalIntegrable (fun x => deriv u x * deriv ψ x) volume l r :=
    intervalIntegrable_iff.mpr (hu.derivative_memLp.integrable_mul hψ.derivative_memLp)
  have hfi : IntervalIntegrable (fun x => f x * ψ x) volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le P.boundary.interval_pos.le).mpr
      ((Lp.memLp f).integrable_mul (hψ.sobolev P.boundary.interval_pos.le).1)
  have hd := piecewise_integral_sum Q.point Q.strictMono.monotone
    (fun x => deriv u x * deriv ψ x) (by simpa only [Q.left_eq, Q.right_eq] using hdi)
  have hf := piecewise_integral_sum Q.point Q.strictMono.monotone
    (fun x => f x * ψ x) (by simpa only [Q.left_eq, Q.right_eq] using hfi)
  simp only [Q.left_eq, Q.right_eq] at hd hf
  have he (e : Fin (n + 1)) := (hj e).poisson_green_identity P.diffusivity_pos.ne'
    (Q.strictMono Fin.castSucc_lt_succ).le (hψ.mono (show
      uIcc (Q.point e.castSucc) (Q.point e.succ) ⊆ uIcc l r by
        rw [uIcc_of_le (Q.strictMono Fin.castSucc_lt_succ).le, uIcc_of_le P.boundary.interval_pos.le]
        exact Icc_subset_Icc (Q.point_mem e.castSucc).1 (Q.point_mem e.succ).2))
  calc
    _ = ∑ e : Fin (n + 1), P.diffusivity *
        (∫ x in Q.point e.castSucc..Q.point e.succ, deriv u x * deriv ψ x) := by
      rw [← hd, Finset.mul_sum]
    _ = ∑ e : Fin (n + 1), ((∫ x in Q.point e.castSucc..Q.point e.succ, f x * ψ x) +
        (P.diffusivity * j e (Q.point e.succ) * ψ (Q.point e.succ) -
          P.diffusivity * j e (Q.point e.castSucc) * ψ (Q.point e.castSucc))) := by
      apply Finset.sum_congr rfl
      intro e _
      linarith [he e]
    _ = _ := by rw [Finset.sum_add_distrib, hf]

theorem PeriodicPointPartition.weak_flux_balance (Q : PeriodicPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r → ψ l = ψ r →
      intervalPointForm P.diffusivity P.strength P.site l r u ψ = ∫ x in l..r, f x * ψ x)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ))
    (ψ : ℝ → ℝ) (hψ : IntervalEnergy ψ l r) (hψp : ψ l = ψ r) :
    (∑ e, (P.diffusivity * j e (Q.point e.succ) * ψ (Q.point e.succ) -
      P.diffusivity * j e (Q.point e.castSucc) * ψ (Q.point e.castSucc))) +
      ∑ i, P.strength i * u (P.site i) * ψ (P.site i) = 0 := by
  have hg := Q.global_green f hu j hj ψ hψ
  have hw := hweak ψ hψ hψp
  unfold intervalPointForm at hw
  linarith

theorem PeriodicPointPartition.node_flux (Q : PeriodicPointPartition P n)
    (j : Fin (n + 1) → ℝ → ℝ) (v : Fin (n + 2)) :
    (∑ e : Fin (n + 1),
      (P.diffusivity * j e (Q.point e.succ) * intervalNodeTest Q.point v (Q.point e.succ) -
       P.diffusivity * j e (Q.point e.castSucc) * intervalNodeTest Q.point v (Q.point e.castSucc))) =
      ∑ e : Fin (n + 1),
      ((if e.succ = v then P.diffusivity * j e (Q.point v) else 0) -
       (if e.castSucc = v then P.diffusivity * j e (Q.point v) else 0)) := by
  apply Finset.sum_congr rfl
  intro e _
  rw [intervalNodeTest_node Q.point Q.strictMono.injective,
    intervalNodeTest_node Q.point Q.strictMono.injective]
  by_cases hs : e.succ = v <;> by_cases hc : e.castSucc = v <;> simp [hs, hc]

theorem PeriodicPointPartition.node_balance (Q : PeriodicPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r → ψ l = ψ r →
      intervalPointForm P.diffusivity P.strength P.site l r u ψ = ∫ x in l..r, f x * ψ x)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) (v : Fin (n + 2))
    (h₀ : v ≠ 0) (h₁ : v ≠ Fin.last (n + 1)) :
    (∑ e : Fin (n + 1),
      ((if e.succ = v then P.diffusivity * j e (Q.point v) else 0) -
       (if e.castSucc = v then P.diffusivity * j e (Q.point v) else 0))) +
      Q.nodeStrength v * u (Q.point v) = 0 := by
  have hb := Q.weak_flux_balance f hu hweak j hj (intervalNodeTest Q.point v)
    (intervalNodeTest_energy_interval Q.point v P.boundary.interval_pos.le) (Q.nodeTest_periodic v h₀ h₁)
  rwa [Q.nodeTest_reaction, Q.node_flux] at hb

end TimeTraps.Analysis
