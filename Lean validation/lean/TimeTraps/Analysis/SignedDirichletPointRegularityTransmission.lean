module

public import TimeTraps.Analysis.SignedDirichletPointRegularityGlobalGreen

@[expose] public section

/-! Signed physical transmission and the mixed endpoint laws. Absorbing
endpoints carry only a zero state trace; slope laws are imposed precisely
at the unselected endpoints. -/

namespace TimeTraps.Analysis

variable {l r : ℝ}

open Set MeasureTheory

structure SignedDirichletPointTransmission {ι : Type*} [Fintype ι] {P : SignedDirichletPointProblem ι l r} {n : ℕ}
    (Q : SignedDirichletPointPartition P n) (u : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ) : Prop where
  zero_boundary : ∀ x ∈ P.boundary.zero_sites, u x = 0
  left_boundary : l ∉ P.boundary.zero_sites →
    P.diffusivity * j 0 l = Q.nodeStrength 0 * u l
  right_boundary : r ∉ P.boundary.zero_sites → P.diffusivity * j (Fin.last n) r =
    -Q.nodeStrength (Fin.last (n + 1)) * u r
  interior_jump : ∀ i : Fin n,
    P.diffusivity * (j i.succ (Q.point i.castSucc.succ) - j i.castSucc (Q.point i.castSucc.succ)) =
      Q.nodeStrength i.castSucc.succ * u (Q.point i.castSucc.succ)

variable {ι : Type*} [Fintype ι] {P : SignedDirichletPointProblem ι l r} {n : ℕ}

theorem SignedDirichletPointPartition.transmission_of_balance (Q : SignedDirichletPointPartition P n)
    (u : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hb : ∀ v : Fin (n + 2), Q.point v ∉ P.boundary.zero_sites →
      (∑ e : Fin (n + 1),
        ((if e.succ = v then P.diffusivity * j e (Q.point v) else 0) -
         (if e.castSucc = v then P.diffusivity * j e (Q.point v) else 0))) +
        Q.nodeStrength v * u (Q.point v) = 0) : SignedDirichletPointTransmission Q u j := by
  constructor
  · exact huz
  · intro hz
    have h := hb 0 (by simpa only [Q.left_eq] using hz)
    have hc (e : Fin (n + 1)) : e.castSucc = (0 : Fin (n + 2)) ↔ e = 0 := by
      simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_zero]
    simp only [Fin.succ_ne_zero, if_false, hc, zero_sub, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Q.left_eq] at h
    linarith
  · intro hz
    have h := hb (Fin.last (n + 1)) (by simpa only [Q.right_eq] using hz)
    have hs (e : Fin (n + 1)) : e.succ = Fin.last (n + 1) ↔ e = Fin.last n := by
      rw [← Fin.succ_last, Fin.succ_inj]
    have hc (e : Fin (n + 1)) : e.castSucc ≠ Fin.last (n + 1) := (Fin.castSucc_lt_last e).ne
    simp only [hs, hc, if_false,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_zero, Q.right_eq] at h
    linarith
  · intro i
    have h := hb i.castSucc.succ (Q.interior_not_zero_site i)
    have hs (e : Fin (n + 1)) : e.succ = i.castSucc.succ ↔ e = i.castSucc := Fin.succ_inj
    have hc (e : Fin (n + 1)) : e.castSucc = i.castSucc.succ ↔ e = i.succ := by
      simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    simp only [Finset.sum_sub_distrib, hs, hc, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    nlinarith

theorem SignedDirichletPointPartition.weak_transmission (Q : SignedDirichletPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r →
      (∀ x ∈ P.boundary.zero_sites, ψ x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u ψ = ∫ x in l..r, f x * ψ x)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) : SignedDirichletPointTransmission Q u j :=
  Q.transmission_of_balance u j huz (Q.node_balance f hu hweak j hj)

theorem SignedDirichletPointTransmission.left_neumann {Q : SignedDirichletPointPartition P n}
    {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ} (h : SignedDirichletPointTransmission Q u j)
    (hz : l ∉ P.boundary.zero_sites) (h₀ : Q.nodeStrength 0 = 0) : j 0 l = 0 := by
  have he := h.left_boundary hz
  rw [h₀, zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left P.diffusivity_pos.ne'

theorem SignedDirichletPointTransmission.right_neumann {Q : SignedDirichletPointPartition P n}
    {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ} (h : SignedDirichletPointTransmission Q u j)
    (hz : r ∉ P.boundary.zero_sites)
    (h₁ : Q.nodeStrength (Fin.last (n + 1)) = 0) : j (Fin.last n) r = 0 := by
  have he := h.right_boundary hz
  rw [h₁, neg_zero, zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left P.diffusivity_pos.ne'

end TimeTraps.Analysis
