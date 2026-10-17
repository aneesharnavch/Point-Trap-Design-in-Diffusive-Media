module

public import TimeTraps.Probability.ReflectedWeakMeanLifetime
public import TimeTraps.Interval.HomogeneousMeanOptimality

@[expose] public section

/-! Stochastic homogeneous design objectives defined from the literal
strict-threshold lifetime. The worst-start objective is the supremum of
its ordinary expectations, and the mean objective averages these over
uniform starting position. Finiteness, state identification, and attainment
are consequences of the proved lifetime theorem and full weak solution. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

def homogeneousLifetimeExpectation (E : IntervalDesign (homogeneous L D hL hD) n K)
    (x : ℝ) : ℝ :=
  ∫ p, (reflectedAtomicLifetimeValue L D x E.geometry.site E.strength p).toReal
    ∂exponentialKillingMeasure brownianDyadicMeasure

def homogeneousLifetimeWorst (E : IntervalDesign (homogeneous L D hL hD) n K) : ℝ :=
  sSup (homogeneousLifetimeExpectation E '' Icc (0 : ℝ) L)

def homogeneousLifetimeMean (E : IntervalDesign (homogeneous L D hL hD) n K) : ℝ :=
  (∫ x in (0 : ℝ)..L, homogeneousLifetimeExpectation E x) / L

theorem homogeneousLifetimeExpectation_eqOn
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    EqOn (homogeneousLifetimeExpectation E) E.state (Icc (0 : ℝ) L) := by
  intro x hx
  exact reflectedWeakMeanTime_lifetime_mean_at_start E hx

theorem homogeneousLifetimeExpectation_weak_equation
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    WeakIntervalEquation E.geometry E.strength (homogeneousLifetimeExpectation E) := by
  apply E.equation.congr_state
  rw [E.homogeneous_source]
  exact (homogeneousLifetimeExpectation_eqOn E).symm

theorem homogeneousLifetimeExpectation_intervalIntegrable
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    IntervalIntegrable (homogeneousLifetimeExpectation E) volume 0 L := by
  have hc := E.equation.energy.continuousOn
  rw [E.homogeneous_source] at hc
  change ContinuousOn E.state (uIcc (0 : ℝ) L) at hc
  have hc' : ContinuousOn E.state (Icc (0 : ℝ) L) := by
    simpa only [uIcc_of_le hL.le] using hc
  exact (hc'.congr (homogeneousLifetimeExpectation_eqOn E)).intervalIntegrable_of_Icc hL.le

theorem homogeneousLifetimeWorst_isGreatest
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    IsGreatest (homogeneousLifetimeExpectation E '' Icc (0 : ℝ) L) E.cost := by
  rw [(homogeneousLifetimeExpectation_eqOn E).image_eq]
  have hm := E.equation.essentialNorm_isGreatest (fun i => (E.strength_pos i).le)
    ⟨⟨0, E.partition.size_pos⟩, E.strength_pos ⟨0, E.partition.size_pos⟩⟩
  rw [E.homogeneous_source] at hm
  exact hm

theorem homogeneousLifetimeWorst_eq
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    homogeneousLifetimeWorst E = E.cost :=
  (homogeneousLifetimeWorst_isGreatest E).csSup_eq

theorem homogeneousLifetimeMean_eq
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    homogeneousLifetimeMean E = E.meanCost := by
  rw [E.homogeneous_meanCost]
  unfold homogeneousLifetimeMean
  apply congrArg (fun z : ℝ => z / L)
  apply intervalIntegral.integral_congr_Ioo_of_le hL.le
  intro x hx
  exact homogeneousLifetimeExpectation_eqOn E (Ioo_subset_Icc_self hx)

end TimeTraps.Probability

end
