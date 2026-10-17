module

public import TimeTraps.Spectral.ArrayBudget

@[expose] public section

/-! Exner's positive-coupling optimum for arbitrary physical arrays on [0,2π).
The complete equality formula allows every common translation consistent
with the sorted representatives, and excludes every nonregular array. -/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem ExnerProblem.regular_site (E : ExnerProblem n) (i : Fin n) :
    E.prescribed.optimalCircle.site i = i.val * (2 * Real.pi) / n :=
  E.budgetProblem.uniform_circle_site i

theorem ExnerProblem.arbitrary_array_upper_bound (E : ExnerProblem n)
    (x : Fin n → ℝ) (hx : E.prescribed.AdmissibleArray x) :
    (E.prescribed.array x hx).principalValue ≤ E.wavenumber ^ 2 := by
  have h := E.prescribed.arbitrary_array_upper_bound x hx
  change (E.prescribed.array x hx).principalValue ≤ 1 * E.wavenumber ^ 2 at h
  simpa only [one_mul] using h

theorem ExnerProblem.array_value_eq_iff_regular (E : ExnerProblem n)
    (x : Fin n → ℝ) (hx : E.prescribed.AdmissibleArray x) :
    (E.prescribed.array x hx).principalValue = E.wavenumber ^ 2 ↔
      ∀ i, x i = (E.prescribed.array x hx).offset + i.val * (2 * Real.pi) / n := by
  have h := E.prescribed.array_value_eq_iff_sites x hx
  change (E.prescribed.array x hx).principalValue = 1 * E.wavenumber ^ 2 ↔ _ at h
  simpa only [one_mul, E.regular_site] using h

theorem ExnerProblem.array_strict_loss (E : ExnerProblem n)
    (x : Fin n → ℝ) (hx : E.prescribed.AdmissibleArray x)
    (hne : ¬ ∀ i, x i = (E.prescribed.array x hx).offset + i.val * (2 * Real.pi) / n) :
    (E.prescribed.array x hx).principalValue < E.wavenumber ^ 2 :=
  lt_of_le_of_ne (E.arbitrary_array_upper_bound x hx)
    (fun he => hne ((E.array_value_eq_iff_regular x hx).mp he))

theorem ExnerProblem.array_maximum (E : ExnerProblem n) :
    IsGreatest E.prescribed.arrayPrincipalValues (E.wavenumber ^ 2) := by
  have h := E.prescribed.array_placement_maximum
  change IsGreatest E.prescribed.arrayPrincipalValues (1 * E.wavenumber ^ 2) at h
  simpa only [one_mul] using h

end TimeTraps.Spectral
