module

public import TimeTraps.Analysis.GeneralIntervalPointRegularityGlobalGreen

@[expose] public section

/-! Signed physical transmission and endpoint conditions, derived from the
full weak equation through the node-selecting polynomial tests. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory

structure IntervalPointTransmission {ι : Type*} [Fintype ι] {P : IntervalPointProblem ι l r} {n : ℕ}
    (Q : IntervalPointPartition P n) (u : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ) : Prop where
  left_boundary : P.diffusivity * j 0 l = Q.nodeStrength 0 * u l
  right_boundary : P.diffusivity * j (Fin.last n) r =
    -Q.nodeStrength (Fin.last (n + 1)) * u r
  interior_jump : ∀ i : Fin n,
    P.diffusivity * (j i.succ (Q.point i.castSucc.succ) - j i.castSucc (Q.point i.castSucc.succ)) =
      Q.nodeStrength i.castSucc.succ * u (Q.point i.castSucc.succ)

variable {ι : Type*} [Fintype ι] {P : IntervalPointProblem ι l r} {n : ℕ}

theorem IntervalPointPartition.transmission_of_balance (Q : IntervalPointPartition P n)
    (u : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ)
    (hb : ∀ v : Fin (n + 2),
      (∑ e : Fin (n + 1),
        ((if e.succ = v then P.diffusivity * j e (Q.point v) else 0) -
         (if e.castSucc = v then P.diffusivity * j e (Q.point v) else 0))) +
        Q.nodeStrength v * u (Q.point v) = 0) : IntervalPointTransmission Q u j := by
  constructor
  · have h := hb 0
    have hc (e : Fin (n + 1)) : e.castSucc = (0 : Fin (n + 2)) ↔ e = 0 := by
      simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_zero]
    simp only [Fin.succ_ne_zero, if_false, hc, zero_sub, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Q.left_eq] at h
    linarith
  · have h := hb (Fin.last (n + 1))
    have hs (e : Fin (n + 1)) : e.succ = Fin.last (n + 1) ↔ e = Fin.last n := by
      rw [← Fin.succ_last, Fin.succ_inj]
    have hc (e : Fin (n + 1)) : e.castSucc ≠ Fin.last (n + 1) := (Fin.castSucc_lt_last e).ne
    simp only [hs, hc, if_false,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_zero, Q.right_eq] at h
    linarith
  · intro i
    have h := hb i.castSucc.succ
    have hs (e : Fin (n + 1)) : e.succ = i.castSucc.succ ↔ e = i.castSucc := Fin.succ_inj
    have hc (e : Fin (n + 1)) : e.castSucc = i.castSucc.succ ↔ e = i.succ := by
      simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    simp only [Finset.sum_sub_distrib, hs, hc, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    nlinarith

theorem IntervalPointPartition.weak_transmission (Q : IntervalPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r →
      intervalPointForm P.diffusivity P.strength P.site l r u ψ = ∫ x in l..r, f x * ψ x)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) : IntervalPointTransmission Q u j :=
  Q.transmission_of_balance u j (Q.node_balance f hu hweak j hj)

theorem IntervalPointTransmission.left_neumann {Q : IntervalPointPartition P n}
    {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ} (h : IntervalPointTransmission Q u j)
    (h₀ : Q.nodeStrength 0 = 0) : j 0 l = 0 := by
  have he := h.left_boundary
  rw [h₀, zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left P.diffusivity_pos.ne'

theorem IntervalPointTransmission.right_neumann {Q : IntervalPointPartition P n}
    {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ} (h : IntervalPointTransmission Q u j)
    (h₁ : Q.nodeStrength (Fin.last (n + 1)) = 0) : j (Fin.last n) r = 0 := by
  have he := h.right_boundary
  rw [h₁, neg_zero, zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left P.diffusivity_pos.ne'

end TimeTraps.Analysis
