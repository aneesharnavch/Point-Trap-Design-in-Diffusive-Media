module

public import TimeTraps.Analysis.GeneralIntervalPointProblem
public import TimeTraps.Spectral.RobinProblem

@[expose] public section

/-! The original finite Robin problem as an actual interval point problem.
The two endpoint labels carry exactly the original Robin coefficients; the
interior contacts, physical length and diffusivity are unchanged. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

def RobinProblem.operatorStrength (P : RobinProblem n) : Fin n ⊕ Fin 2 → ℝ :=
  Sum.elim P.strength (fun e => if e = 0 then P.betaLeft else P.betaRight)

def RobinProblem.operatorSite (P : RobinProblem n) : Fin n ⊕ Fin 2 → ℝ :=
  Sum.elim P.site (fun e => if e = 0 then 0 else P.length)

def RobinProblem.intervalPointProblem (P : RobinProblem n) :
    IntervalPointProblem (Fin n ⊕ Fin 2) 0 P.length where
  interval_pos := P.length_pos
  diffusivity := P.diffusivity
  diffusivity_pos := P.diffusivity_pos
  strength := P.operatorStrength
  strength_nonneg := by
    intro i
    rcases i with i | e
    · exact (P.strength_pos i).le
    · change 0 ≤ if e = 0 then P.betaLeft else P.betaRight
      split
      · exact P.betaLeft_nonneg
      · exact P.betaRight_nonneg
  site := P.operatorSite
  site_mem := by
    intro i
    rcases i with i | e
    · exact Ioo_subset_Icc_self (P.site_interior i)
    · change (if e = 0 then 0 else P.length) ∈ Icc (0 : ℝ) P.length
      split
      · exact ⟨le_rfl, P.length_pos.le⟩
      · exact ⟨P.length_pos.le, le_rfl⟩
  positive_contact := ⟨Sum.inl ⟨0, P.count_pos⟩, P.strength_pos _⟩

theorem RobinProblem.operator_pointForm (P : RobinProblem n) (u v : ℝ → ℝ) :
    intervalPointForm P.diffusivity P.operatorStrength P.operatorSite 0 P.length u v =
      P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x) +
        (∑ i, P.strength i * u (P.site i) * v (P.site i)) +
        P.betaLeft * u 0 * v 0 + P.betaRight * u P.length * v P.length := by
  simp only [intervalPointForm, Fintype.sum_sum_type, operatorStrength, operatorSite,
    Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two]
  simp only [ite_true, Fin.isValue, one_ne_zero, ite_false]
  ring

theorem RobinProblem.operator_quadraticForm (P : RobinProblem n) (u : ℝ → ℝ) :
    intervalPointForm P.diffusivity P.operatorStrength P.operatorSite 0 P.length u u =
      P.quadraticForm u := by
  rw [P.operator_pointForm]
  simp only [RobinProblem.quadraticForm, SpectralProblem.quadraticForm, pow_two, mul_assoc]

theorem RobinProblem.interval_squareMass (P : RobinProblem n)
    (u : IntervalSobolevSpace 0 P.length) :
    P.squareMass (u.representative P.length_pos) = ‖u.state‖ ^ 2 := by
  rw [RobinProblem.squareMass, SpectralProblem.squareMass,
    ← real_inner_self_eq_norm_sq, state_inner _ _ P.length_pos]
  simp only [pow_two]

end TimeTraps.Spectral
