module

public import TimeTraps.Analysis.IntervalPeriodicRegularityTransmission

@[expose] public section

/-! The strong-to-weak direction uses the actual AC Green identity on every
piece. Signed transmission and endpoint laws cancel all boundary terms. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {P : PeriodicPointProblem ι l r} {n : ℕ}

theorem PeriodicPointPartition.reaction_node_sum (Q : PeriodicPointPartition P n)
    (u ψ : ℝ → ℝ) :
    (∑ i, P.strength i * u (P.site i) * ψ (P.site i)) =
      ∑ v, Q.nodeStrength v * u (Q.point v) * ψ (Q.point v) := by
  classical
  unfold nodeStrength
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Q.contact_eq i]
  simp only [ite_mul, zero_mul]
  simp

theorem PeriodicPointTransmission.flux_balance {Q : PeriodicPointPartition P n}
    {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ} (h : PeriodicPointTransmission Q u j)
    (ψ : ℝ → ℝ) (hψp : ψ l = ψ r) :
    (∑ e, (P.diffusivity * j e (Q.point e.succ) * ψ (Q.point e.succ) -
      P.diffusivity * j e (Q.point e.castSucc) * ψ (Q.point e.castSucc))) +
      ∑ i, P.strength i * u (P.site i) * ψ (P.site i) = 0 := by
  rw [Q.reaction_node_sum, Finset.sum_sub_distrib,
    Fin.sum_univ_castSucc (fun e : Fin (n + 1) =>
      P.diffusivity * j e (Q.point e.succ) * ψ (Q.point e.succ)),
    Fin.sum_univ_succ (fun e : Fin (n + 1) =>
      P.diffusivity * j e (Q.point e.castSucc) * ψ (Q.point e.castSucc)),
    Fin.sum_univ_succ (fun v : Fin (n + 2) =>
      Q.nodeStrength v * u (Q.point v) * ψ (Q.point v)),
    Fin.sum_univ_castSucc (fun v : Fin (n + 1) =>
      Q.nodeStrength v.succ * u (Q.point v.succ) * ψ (Q.point v.succ))]
  simp only [Fin.castSucc_zero, Fin.succ_last, Q.left_eq, Q.right_eq]
  have he (i : Fin n) :
      P.diffusivity * j i.castSucc (Q.point i.castSucc.succ) * ψ (Q.point i.castSucc.succ) -
      P.diffusivity * j i.succ (Q.point i.succ.castSucc) * ψ (Q.point i.succ.castSucc) +
      Q.nodeStrength i.castSucc.succ * u (Q.point i.castSucc.succ) *
        ψ (Q.point i.castSucc.succ) = 0 := by
    rw [← Fin.succ_castSucc]
    nlinarith [congrArg (fun x : ℝ => x * ψ (Q.point i.castSucc.succ)) (h.interior_jump i)]
  have hi := Finset.sum_eq_zero (fun i (_ : i ∈ Finset.univ) => he i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hi
  have hs := congrArg (fun x : ℝ => x * ψ l) h.seam_jump
  rw [← h.periodic_state, ← hψp]
  nlinarith

theorem PeriodicPointPartition.weak_of_piecewise (Q : PeriodicPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) (ht : PeriodicPointTransmission Q u j) :
    ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r → ψ l = ψ r →
      intervalPointForm P.diffusivity P.strength P.site l r u ψ = ∫ x in l..r, f x * ψ x := by
  intro ψ hψ hψp
  have hg := Q.global_green f hu j hj ψ hψ
  have hb := ht.flux_balance ψ hψp
  unfold intervalPointForm
  linarith

end TimeTraps.Analysis
