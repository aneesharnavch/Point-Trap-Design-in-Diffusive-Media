module

public import TimeTraps.Analysis.IntervalPointRegularityGlobalGreen

@[expose] public section

/-! Signed physical transmission and endpoint conditions, derived from the
full weak equation through the node-selecting polynomial tests. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

structure UnitPointTransmission {ι : Type*} [Fintype ι] {P : UnitPointProblem ι} {n : ℕ}
    (Q : UnitPointPartition P n) (u : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ) : Prop where
  left_boundary : P.diffusivity * j 0 0 = Q.nodeStrength 0 * u 0
  right_boundary : P.diffusivity * j (Fin.last n) 1 =
    -Q.nodeStrength (Fin.last (n + 1)) * u 1
  interior_jump : ∀ i : Fin n,
    P.diffusivity * (j i.succ (Q.point i.castSucc.succ) - j i.castSucc (Q.point i.castSucc.succ)) =
      Q.nodeStrength i.castSucc.succ * u (Q.point i.castSucc.succ)

variable {ι : Type*} [Fintype ι] {P : UnitPointProblem ι} {n : ℕ}

theorem UnitPointPartition.transmission_of_balance (Q : UnitPointPartition P n)
    (u : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ)
    (hb : ∀ v : Fin (n + 2),
      (∑ e : Fin (n + 1),
        ((if e.succ = v then P.diffusivity * j e (Q.point v) else 0) -
         (if e.castSucc = v then P.diffusivity * j e (Q.point v) else 0))) +
        Q.nodeStrength v * u (Q.point v) = 0) : UnitPointTransmission Q u j := by
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

theorem UnitPointPartition.weak_transmission (Q : UnitPointPartition P n)
    (f : UnitIntervalL2) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ 0 1 →
      unitPointForm P.diffusivity P.strength P.site u ψ = ∫ x in (0 : ℝ)..1, f x * ψ x)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) : UnitPointTransmission Q u j :=
  Q.transmission_of_balance u j (Q.node_balance f hu hweak j hj)

theorem UnitPointTransmission.left_neumann {Q : UnitPointPartition P n}
    {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ} (h : UnitPointTransmission Q u j)
    (h₀ : Q.nodeStrength 0 = 0) : j 0 0 = 0 := by
  have he := h.left_boundary
  rw [h₀, zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left P.diffusivity_pos.ne'

theorem UnitPointTransmission.right_neumann {Q : UnitPointPartition P n}
    {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ} (h : UnitPointTransmission Q u j)
    (h₁ : Q.nodeStrength (Fin.last (n + 1)) = 0) : j (Fin.last n) 1 = 0 := by
  have he := h.right_boundary
  rw [h₁, neg_zero, zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left P.diffusivity_pos.ne'

end TimeTraps.Analysis
