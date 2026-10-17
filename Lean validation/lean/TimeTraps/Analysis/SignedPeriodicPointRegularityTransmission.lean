module

public import TimeTraps.Analysis.SignedPeriodicPointRegularitySeam

@[expose] public section

/-! Periodic transmission consists of matching state traces, one combined
seam flux law, and the signed interior jumps. There are no independent
left and right endpoint slope conditions. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {l r : ℝ}

structure SignedPeriodicPointTransmission {ι : Type*} [Fintype ι] {P : SignedPeriodicPointProblem ι l r} {n : ℕ}
    (Q : SignedPeriodicPointPartition P n) (u : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ) : Prop where
  periodic_state : u l = u r
  seam_jump : P.diffusivity * (j 0 l - j (Fin.last n) r) =
    (Q.nodeStrength 0 + Q.nodeStrength (Fin.last (n + 1))) * u l
  interior_jump : ∀ i : Fin n,
    P.diffusivity * (j i.succ (Q.point i.castSucc.succ) - j i.castSucc (Q.point i.castSucc.succ)) =
      Q.nodeStrength i.castSucc.succ * u (Q.point i.castSucc.succ)

variable {ι : Type*} [Fintype ι] {P : SignedPeriodicPointProblem ι l r} {n : ℕ}

theorem SignedPeriodicPointPartition.transmission_of_balance (Q : SignedPeriodicPointPartition P n)
    (u : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ) (hup : u l = u r)
    (hseam : P.diffusivity * j (Fin.last n) r - P.diffusivity * j 0 l +
      Q.nodeStrength 0 * u l + Q.nodeStrength (Fin.last (n + 1)) * u r = 0)
    (hb : ∀ v : Fin (n + 2), v ≠ 0 → v ≠ Fin.last (n + 1) →
      (∑ e : Fin (n + 1),
        ((if e.succ = v then P.diffusivity * j e (Q.point v) else 0) -
         (if e.castSucc = v then P.diffusivity * j e (Q.point v) else 0))) +
        Q.nodeStrength v * u (Q.point v) = 0) : SignedPeriodicPointTransmission Q u j := by
  refine ⟨hup, ?_, ?_⟩
  · rw [← hup] at hseam
    nlinarith
  · intro i
    have h₀ : i.castSucc.succ ≠ (0 : Fin (n + 2)) := Fin.succ_ne_zero _
    have h₁ : i.castSucc.succ ≠ Fin.last (n + 1) := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
      omega
    have h := hb i.castSucc.succ h₀ h₁
    have hs (e : Fin (n + 1)) : e.succ = i.castSucc.succ ↔ e = i.castSucc := Fin.succ_inj
    have hc (e : Fin (n + 1)) : e.castSucc = i.castSucc.succ ↔ e = i.succ := by
      simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    simp only [Finset.sum_sub_distrib, hs, hc, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    nlinarith

theorem SignedPeriodicPointPartition.weak_transmission (Q : SignedPeriodicPointPartition P n)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hup : u l = u r)
    (hweak : ∀ ψ : ℝ → ℝ, IntervalEnergy ψ l r → ψ l = ψ r →
      intervalPointForm P.diffusivity P.strength P.site l r u ψ = ∫ x in l..r, f x * ψ x)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) : SignedPeriodicPointTransmission Q u j :=
  Q.transmission_of_balance u j hup (Q.seam_balance f hu hweak j hj) (Q.node_balance f hu hweak j hj)

theorem SignedPeriodicPointTransmission.seam_neumann {Q : SignedPeriodicPointPartition P n}
    {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ} (h : SignedPeriodicPointTransmission Q u j)
    (hzero : Q.nodeStrength 0 + Q.nodeStrength (Fin.last (n + 1)) = 0) :
    j 0 l = j (Fin.last n) r := by
  have he := h.seam_jump
  rw [hzero, zero_mul] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left P.diffusivity_pos.ne')

end TimeTraps.Analysis
