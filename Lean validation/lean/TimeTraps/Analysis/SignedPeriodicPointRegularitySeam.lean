module

public import TimeTraps.Analysis.SignedPeriodicPointRegularityGlobalGreen

@[expose] public section

/-! A single admissible periodic test, formed by adding the two endpoint
Lagrange tests, extracts the seam balance. Endpoint contacts remain separate
labels until their two aggregate strengths enter the same seam equation. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {l r : ℝ} {ι : Type*} [Fintype ι] {P : SignedPeriodicPointProblem ι l r} {n : ℕ}

theorem SignedPeriodicPointPartition.seam_balance (Q : SignedPeriodicPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r → ψ l = ψ r →
      intervalPointForm P.diffusivity P.strength P.site l r u ψ = ∫ x in l..r, f x * ψ x)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) :
    P.diffusivity * j (Fin.last n) r - P.diffusivity * j 0 l +
      Q.nodeStrength 0 * u l + Q.nodeStrength (Fin.last (n + 1)) * u r = 0 := by
  have hp : Q.seamTest l = Q.seamTest r := Q.seamTest_endpoints.1.trans Q.seamTest_endpoints.2.symm
  have hb := Q.weak_flux_balance f hu hweak j hj Q.seamTest Q.seamTest_energy hp
  have hreaction : (∑ i, P.strength i * u (P.site i) * Q.seamTest (P.site i)) =
      Q.nodeStrength 0 * u l + Q.nodeStrength (Fin.last (n + 1)) * u r := by
    simp only [SignedPeriodicPointPartition.seamTest, mul_add, Finset.sum_add_distrib]
    rw [Q.nodeTest_reaction, Q.nodeTest_reaction, Q.left_eq, Q.right_eq]
  have hflux : (∑ e : Fin (n + 1),
      (P.diffusivity * j e (Q.point e.succ) * Q.seamTest (Q.point e.succ) -
       P.diffusivity * j e (Q.point e.castSucc) * Q.seamTest (Q.point e.castSucc))) =
      (∑ e : Fin (n + 1),
        (P.diffusivity * j e (Q.point e.succ) * intervalNodeTest Q.point 0 (Q.point e.succ) -
         P.diffusivity * j e (Q.point e.castSucc) * intervalNodeTest Q.point 0 (Q.point e.castSucc))) +
      (∑ e : Fin (n + 1),
        (P.diffusivity * j e (Q.point e.succ) * intervalNodeTest Q.point (Fin.last (n + 1)) (Q.point e.succ) -
         P.diffusivity * j e (Q.point e.castSucc) * intervalNodeTest Q.point (Fin.last (n + 1)) (Q.point e.castSucc))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    simp only [SignedPeriodicPointPartition.seamTest]
    ring
  rw [hreaction, hflux, Q.node_flux, Q.node_flux] at hb
  have hc (e : Fin (n + 1)) : e.castSucc = (0 : Fin (n + 2)) ↔ e = 0 := by
    simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_zero]
  have hs (e : Fin (n + 1)) : e.succ = Fin.last (n + 1) ↔ e = Fin.last n := by
    rw [← Fin.succ_last, Fin.succ_inj]
  have hn (e : Fin (n + 1)) : e.castSucc ≠ Fin.last (n + 1) := (Fin.castSucc_lt_last e).ne
  simp only [Fin.succ_ne_zero, if_false, hc, hs, hn, zero_sub, sub_zero,
    Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Q.left_eq, Q.right_eq] at hb
  linarith

end TimeTraps.Analysis
