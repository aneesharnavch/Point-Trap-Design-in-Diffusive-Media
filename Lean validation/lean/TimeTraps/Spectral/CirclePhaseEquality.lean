module

public import TimeTraps.Spectral.CirclePhase

@[expose] public section

/-! Equality in the global phase bound forces the exact incident phases at
all physical traps. The assertions concern arbitrary positive eigenstates. -/

namespace TimeTraps.Spectral.CircleProblem

open Set
open scoped BigOperators

variable {n : ℕ} {P : CircleProblem n} {ev k : ℝ}

theorem phase_global_eq_iff (E : PositiveNetworkEigenstate P.network ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) :
    P.length * k = 2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k)) ↔
      ∀ i : Fin n, E.phase k i 0 = -E.phase k ((finRotate n).symm i) (P.gap ((finRotate n).symm i)) := by
  let loss := fun i : Fin n => 2 * Real.arctan (P.strength i / (2 * P.diffusivity * k)) -
    (E.phase k i 0 - E.phase k ((finRotate n).symm i) (P.gap ((finRotate n).symm i)))
  have hloss (i : Fin n) : 0 ≤ loss i := sub_nonneg.mpr (phase_jump_sharp E hk i).1
  have hsum : (∑ i, loss i) =
      2 * (∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k))) - P.length * k := by
    dsimp only [loss]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← phase_sum E hk hk2, mul_comm k]
  constructor
  · intro he
    have hz : (∑ i, loss i) = 0 := by rw [hsum, he, sub_self]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hloss i)).mp hz
    intro i
    apply (phase_jump_sharp E hk i).2.mp
    have hi := hall i (Finset.mem_univ i)
    dsimp only [loss] at hi
    linarith
  · intro hall
    rw [mul_comm P.length, phase_sum E hk hk2, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => (phase_jump_sharp E hk i).2.mpr (hall i))

theorem symmetric_phase_values (E : PositiveNetworkEigenstate P.network ev)
    (i : Fin n)
    (hs : E.phase k i 0 = -E.phase k ((finRotate n).symm i) (P.gap ((finRotate n).symm i))) :
    E.phase k i 0 = Real.arctan (P.strength i / (2 * P.diffusivity * k)) ∧
    E.phase k ((finRotate n).symm i) (P.gap ((finRotate n).symm i)) = -Real.arctan (P.strength i / (2 * P.diffusivity * k)) := by
  have hj := phase_tan_jump (k := k) E i
  have hm : E.phase k ((finRotate n).symm i) (P.gap ((finRotate n).symm i)) = -E.phase k i 0 := by linarith
  rw [hm, Real.tan_neg] at hj
  have ht : Real.tan (E.phase k i 0) = P.strength i / (2 * P.diffusivity * k) := by
    have he : P.strength i / (P.diffusivity * k) = 2 * (P.strength i / (2 * P.diffusivity * k)) := by ring
    rw [he] at hj
    linarith
  have hp : E.phase k i 0 = Real.arctan (P.strength i / (2 * P.diffusivity * k)) := by
    rw [← ht, Real.arctan_tan (E.phase_branch k i 0).1 (E.phase_branch k i 0).2]
  exact ⟨hp, by rw [hm, hp]⟩

theorem phase_values_of_global_eq (E : PositiveNetworkEigenstate P.network ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity)
    (he : P.length * k = 2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k))) (i : Fin n) :
    E.phase k i 0 = Real.arctan (P.strength i / (2 * P.diffusivity * k)) ∧
    E.phase k ((finRotate n).symm i) (P.gap ((finRotate n).symm i)) = -Real.arctan (P.strength i / (2 * P.diffusivity * k)) :=
  symmetric_phase_values E i ((phase_global_eq_iff E hk hk2).mp he i)

end TimeTraps.Spectral.CircleProblem
