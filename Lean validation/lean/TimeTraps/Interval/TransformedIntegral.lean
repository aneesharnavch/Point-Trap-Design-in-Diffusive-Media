module

public import TimeTraps.Interval.GlobalState
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

@[expose] public section

/-!
Exact integration across the finite set of traps. Continuity and the actual
derivative away from those sites meet Mathlib's fundamental theorem with a
countable exceptional set. Absolute continuity is then a consequence of the
integral representation, rather than an assumed property of the assembled state.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators Classical

variable {n : ℕ}

theorem OrderedMedium.absorptionCDF_integrable (D : OrderedMedium n) (p : Fin n → ℝ) (a b : ℝ) :
    IntervalIntegrable (D.absorptionCDF p) volume a b := by
  have hi : ∀ i : Fin n, IntervalIntegrable (fun z => if D.sourceSite i ≤ z then p i else 0) volume a b := by
    intro i
    have hc : IntervalIntegrable (fun _ : ℝ => p i) volume a b := intervalIntegrable_const
    have he : (Ici (D.sourceSite i)).indicator (fun _ : ℝ => p i) =
        (fun z => if D.sourceSite i ≤ z then p i else 0) := by
      funext z
      simp only [Set.indicator, mem_Ici]
    constructor
    · rw [← he]
      exact hc.1.indicator measurableSet_Ici
    · rw [← he]
      exact hc.2.indicator measurableSet_Ici
  have hs := IntervalIntegrable.sum Finset.univ (fun i _ => hi i)
  have he : (∑ i : Fin n, fun z => if D.sourceSite i ≤ z then p i else 0) = D.absorptionCDF p := by
    funext z
    simp only [OrderedMedium.absorptionCDF, Finset.sum_apply]
  rw [he] at hs
  exact hs

noncomputable def OrderedMedium.transformedSlope (D : OrderedMedium n)
    (κ : Fin n → ℝ) (U : Fin (n + 2) → ℝ) (z : ℝ) : ℝ :=
  D.source.weight D.conductance z * (D.absorptionCDF (D.absorptionShare κ U) z - z)

theorem OrderedMedium.transformedSlope_integrable (D : OrderedMedium n)
    (κ : Fin n → ℝ) (U : Fin (n + 2) → ℝ) (a b : ℝ) :
    IntervalIntegrable (D.transformedSlope κ U) volume a b := by
  have hw := D.source.weight_continuous D.conductance_continuous D.conductance_pos
  exact ((D.absorptionCDF_integrable (D.absorptionShare κ U) a b).sub
    (continuous_id.intervalIntegrable a b)).continuousOn_mul hw.continuousOn

/-- Exact state differences across arbitrary subintervals, including any
number of trap sites and either physical endpoint. -/
theorem OrderedMedium.transformedState_integral (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    (∫ z in a..b, D.transformedSlope κ U z) = D.transformedState U u b - D.transformedState U u a := by
  apply integral_eq_of_hasDerivAt_off_countable_of_le _ _ hab
    (Set.finite_range D.sourceSite).countable (D.transformedState_continuous h.energy_membership).continuousOn
  · intro z hz
    apply D.transformedState_derivative h ⟨ha.trans_lt hz.1.1, hz.1.2.trans_le hb⟩
    intro i hi
    exact hz.2 ⟨i, hi⟩
  · exact D.transformedSlope_integrable κ U a b

theorem OrderedMedium.transformedState_absolutelyContinuous (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) :
    AbsolutelyContinuousOnInterval (D.transformedState U u) 0 1 := by
  have hi := D.transformedSlope_integrable κ U 0 1
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 1)
  have hac := (interval_absolutelyContinuous_const (D.transformedState U u 0) 0 1).fun_add hp
  apply interval_absolutelyContinuous_congr hac
  intro z hz
  have hz' : z ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hz
  have he := D.transformedState_integral h le_rfl hz'.2 hz'.1
  change D.transformedState U u 0 + (∫ t in 0..z, D.transformedSlope κ U t) = D.transformedState U u z
  linarith

theorem OrderedMedium.weak_transformedState_integral (D : OrderedMedium n) {κ : Fin n → ℝ}
    {U : Fin (n + 2) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (h : WeakGraphEquation D.graph (nodalStrength κ) U u)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    (∫ z in a..b, D.transformedSlope κ U z) = D.transformedState U u b - D.transformedState U u a := by
  obtain ⟨j, hj⟩ := h.to_strong (nodalStrength_nonneg κ hκ) (nodalStrength_anchor κ hanchor)
  exact D.transformedState_integral hj ha hb hab

end TimeTraps.Interval
