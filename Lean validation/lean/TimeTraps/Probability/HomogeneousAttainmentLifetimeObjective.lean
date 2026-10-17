module

public import TimeTraps.Probability.HomogeneousAttainmentLifetime

@[expose] public section

/-! Worst-start and uniform-start objectives defined from literal
first-attainment expectations. Their equality with the independent
physical state objectives follows from the proved lifetime identity.
The worst-start supremum is attained on the original closed interval. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Interval

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

def homogeneousAttainmentLifetimeWorst
    (E : IntervalDesign (homogeneous L D hL hD) n K) : ℝ :=
  sSup (homogeneousAttainmentLifetimeExpectation E '' Icc (0 : ℝ) L)

def homogeneousAttainmentLifetimeMean
    (E : IntervalDesign (homogeneous L D hL hD) n K) : ℝ :=
  (∫ x in (0 : ℝ)..L, homogeneousAttainmentLifetimeExpectation E x) / L

theorem homogeneousAttainmentLifetimeWorst_eq_strict
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    homogeneousAttainmentLifetimeWorst E = homogeneousLifetimeWorst E := by
  have he : homogeneousAttainmentLifetimeExpectation E = homogeneousLifetimeExpectation E :=
    funext (homogeneousAttainmentLifetimeExpectation_eq E)
  unfold homogeneousAttainmentLifetimeWorst homogeneousLifetimeWorst
  rw [he]

theorem homogeneousAttainmentLifetimeMean_eq_strict
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    homogeneousAttainmentLifetimeMean E = homogeneousLifetimeMean E := by
  have he : homogeneousAttainmentLifetimeExpectation E = homogeneousLifetimeExpectation E :=
    funext (homogeneousAttainmentLifetimeExpectation_eq E)
  unfold homogeneousAttainmentLifetimeMean homogeneousLifetimeMean
  rw [he]

theorem homogeneousAttainmentLifetimeWorst_isGreatest
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    IsGreatest (homogeneousAttainmentLifetimeExpectation E '' Icc (0 : ℝ) L) E.cost := by
  have he : homogeneousAttainmentLifetimeExpectation E = homogeneousLifetimeExpectation E :=
    funext (homogeneousAttainmentLifetimeExpectation_eq E)
  rw [he]
  exact homogeneousLifetimeWorst_isGreatest E

theorem homogeneousAttainmentLifetimeWorst_eq
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    homogeneousAttainmentLifetimeWorst E = E.cost :=
  (homogeneousAttainmentLifetimeWorst_eq_strict E).trans (homogeneousLifetimeWorst_eq E)

theorem homogeneousAttainmentLifetimeMean_eq
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    homogeneousAttainmentLifetimeMean E = E.meanCost :=
  (homogeneousAttainmentLifetimeMean_eq_strict E).trans (homogeneousLifetimeMean_eq E)

end TimeTraps.Probability

end
