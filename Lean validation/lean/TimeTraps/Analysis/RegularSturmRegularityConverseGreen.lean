module

public import TimeTraps.Analysis.RegularSturmRegularityTransmission

@[expose] public section

/-! The strong-to-weak direction uses the actual AC Green identity on every
piece. Signed transmission and endpoint laws cancel all boundary terms. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {P : RegularSturmProblem ι l r} {n : ℕ}

theorem RegularSturmPartition.reaction_node_sum (Q : RegularSturmPartition P n)
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

theorem RegularSturmTransmission.flux_balance {Q : RegularSturmPartition P n}
    {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ} (h : RegularSturmTransmission Q u j)
    (ψ : ℝ → ℝ) (hψz : ∀ x ∈ P.boundary.zero_sites, ψ x = 0) :
    (∑ e, (j e (Q.point e.succ) * ψ (Q.point e.succ) -
      j e (Q.point e.castSucc) * ψ (Q.point e.castSucc))) +
      ∑ i, P.strength i * u (P.site i) * ψ (P.site i) = 0 := by
  rw [Q.reaction_node_sum, Finset.sum_sub_distrib,
    Fin.sum_univ_castSucc (fun e : Fin (n + 1) =>
      j e (Q.point e.succ) * ψ (Q.point e.succ)),
    Fin.sum_univ_succ (fun e : Fin (n + 1) =>
      j e (Q.point e.castSucc) * ψ (Q.point e.castSucc)),
    Fin.sum_univ_succ (fun v : Fin (n + 2) =>
      Q.nodeStrength v * u (Q.point v) * ψ (Q.point v)),
    Fin.sum_univ_castSucc (fun v : Fin (n + 1) =>
      Q.nodeStrength v.succ * u (Q.point v.succ) * ψ (Q.point v.succ))]
  simp only [Fin.castSucc_zero, Fin.succ_last, Q.left_eq, Q.right_eq]
  have he (i : Fin n) :
      j i.castSucc (Q.point i.castSucc.succ) * ψ (Q.point i.castSucc.succ) -
      j i.succ (Q.point i.succ.castSucc) * ψ (Q.point i.succ.castSucc) +
      Q.nodeStrength i.castSucc.succ * u (Q.point i.castSucc.succ) *
        ψ (Q.point i.castSucc.succ) = 0 := by
    rw [← Fin.succ_castSucc]
    nlinarith [congrArg (fun x : ℝ => x * ψ (Q.point i.castSucc.succ)) (h.interior_jump i)]
  have hi := Finset.sum_eq_zero (fun i (_ : i ∈ Finset.univ) => he i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hi
  have hl : j 0 l * ψ l = Q.nodeStrength 0 * u l * ψ l := by
    by_cases hz : l ∈ P.boundary.zero_sites
    · rw [hψz l hz, mul_zero, mul_zero]
    · exact congrArg (fun x : ℝ => x * ψ l) (h.left_boundary hz)
  have hr : j (Fin.last n) r * ψ r =
      -Q.nodeStrength (Fin.last (n + 1)) * u r * ψ r := by
    by_cases hz : r ∈ P.boundary.zero_sites
    · rw [hψz r hz, mul_zero, mul_zero]
    · exact congrArg (fun x : ℝ => x * ψ r) (h.right_boundary hz)
  nlinarith

theorem RegularSturmPartition.weak_of_piecewise (Q : RegularSturmPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalFluxRegularity u (j e) (fun x => P.potential x * u x - f x * Real.sqrt (P.speed x)) P.conductance
      (Q.point e.castSucc) (Q.point e.succ)) (ht : RegularSturmTransmission Q u j) :
    ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r →
      (∀ x ∈ P.boundary.zero_sites, ψ x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u ψ = ∫ x in l..r, f x * Real.sqrt (P.speed x) * ψ x := by
  intro ψ hψ hψz
  have hg := Q.global_green f hu j hj ψ hψ
  have hb := ht.flux_balance ψ hψz
  unfold regularSturmPhysicalForm
  linarith

end TimeTraps.Analysis
