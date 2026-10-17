module

public import TimeTraps.Spectral.RobinPhaseEvolution

@[expose] public section

/-! Equality in the global phase bound forces the exact incident phases at
all physical traps. The assertions concern arbitrary positive eigenstates. -/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

variable {n : ℕ} {P : RobinProblem n} {ev k : ℝ}

theorem PositiveRobinEigenstate.phase_global_eq_iff (E : PositiveRobinEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) :
    P.length * k = Real.arctan (P.betaLeft / (P.diffusivity * k)) +
      Real.arctan (P.betaRight / (P.diffusivity * k)) +
        2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k)) ↔
      ∀ i : Fin n, E.phase k i.succ 0 = -E.phase k i.castSucc (P.shooting.gap i.castSucc) := by
  let loss := fun i : Fin n => 2 * Real.arctan (P.strength i / (2 * P.diffusivity * k)) -
    (E.phase k i.succ 0 - E.phase k i.castSucc (P.shooting.gap i.castSucc))
  have hloss (i : Fin n) : 0 ≤ loss i := sub_nonneg.mpr (E.phase_jump_sharp hk i).1
  have hsum : (∑ i, loss i) =
      Real.arctan (P.betaLeft / (P.diffusivity * k)) +
      Real.arctan (P.betaRight / (P.diffusivity * k)) +
        2 * (∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k))) - P.length * k := by
    dsimp only [loss]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h := E.phase_sum hk hk2
    linarith
  constructor
  · intro he
    have hz : (∑ i, loss i) = 0 := by rw [hsum, he, sub_self]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hloss i)).mp hz
    intro i
    apply (E.phase_jump_sharp hk i).2.mp
    have hi := hall i (Finset.mem_univ i)
    dsimp only [loss] at hi
    linarith
  · intro hall
    rw [mul_comm P.length, E.phase_sum hk hk2, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => (E.phase_jump_sharp hk i).2.mpr (hall i))

theorem PositiveRobinEigenstate.symmetric_phase_values (E : PositiveRobinEigenstate P ev)
    (hk : 0 < k) (i : Fin n)
    (hs : E.phase k i.succ 0 = -E.phase k i.castSucc (P.shooting.gap i.castSucc)) :
    E.phase k i.succ 0 = Real.arctan (P.strength i / (2 * P.diffusivity * k)) ∧
    E.phase k i.castSucc (P.shooting.gap i.castSucc) = -Real.arctan (P.strength i / (2 * P.diffusivity * k)) := by
  have hj := E.phase_tan_jump hk i
  have hm : E.phase k i.castSucc (P.shooting.gap i.castSucc) = -E.phase k i.succ 0 := by linarith
  rw [hm, Real.tan_neg] at hj
  have ht : Real.tan (E.phase k i.succ 0) = P.strength i / (2 * P.diffusivity * k) := by
    have he : P.strength i / (P.diffusivity * k) = 2 * (P.strength i / (2 * P.diffusivity * k)) := by ring
    rw [he] at hj
    linarith
  have hp : E.phase k i.succ 0 = Real.arctan (P.strength i / (2 * P.diffusivity * k)) := by
    rw [← ht, Real.arctan_tan (E.phase_branch k i.succ 0).1 (E.phase_branch k i.succ 0).2]
  exact ⟨hp, by rw [hm, hp]⟩

theorem PositiveRobinEigenstate.phase_values_of_global_eq (E : PositiveRobinEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity)
    (he : P.length * k = Real.arctan (P.betaLeft / (P.diffusivity * k)) +
      Real.arctan (P.betaRight / (P.diffusivity * k)) +
        2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k))) (i : Fin n) :
    E.phase k i.succ 0 = Real.arctan (P.strength i / (2 * P.diffusivity * k)) ∧
    E.phase k i.castSucc (P.shooting.gap i.castSucc) = -Real.arctan (P.strength i / (2 * P.diffusivity * k)) :=
  E.symmetric_phase_values hk i ((E.phase_global_eq_iff hk hk2).mp he i)

end TimeTraps.Spectral
