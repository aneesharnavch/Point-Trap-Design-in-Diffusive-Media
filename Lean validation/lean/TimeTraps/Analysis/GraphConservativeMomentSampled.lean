module

public import TimeTraps.Analysis.GraphConservativeMomentSampledData

@[expose] public section

/-! Uniform scalar fourth increments of the actual countably sampled graph
law. The time labels may repeat or occur in either order. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_scalar_fourth_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (τ : ℕ → ℝ≥0) (x : GraphRealization P.geometry)
    (f : C(GraphRealization P.geometry, ℝ)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (T : ℝ≥0) (y : GraphRealization P.geometry),
      (∫ z, (f z - f y) ^ 4 ∂P.realizedTransition T y) ≤ C * T.val ^ 2)
    (i j : ℕ) :
    (∫ q, (f (q j) - f (q i)) ^ 4 ∂P.sampledPathLaw hκ τ x) ≤
      C * dist (τ i) (τ j) ^ 2 := by
  have hd {s t : ℝ≥0} (hst : s ≤ t) : (t - s).val = dist s t := by
    calc
      _ = (t : ℝ) - (s : ℝ) := NNReal.coe_sub hst
      _ = dist s t := by
        rw [NNReal.dist_eq, abs_sub_comm]
        have hstR : (s : ℝ) ≤ (t : ℝ) := hst
        exact (abs_of_nonneg (sub_nonneg.mpr hstR)).symm
  rcases lt_trichotomy (τ i) (τ j) with hij | hij | hij
  · exact (P.sampledPathLaw_scalar_fourth_ordered hκ τ x f hC i j hij).trans_eq
      (congrArg (fun r : ℝ => C * r ^ 2) (hd hij.le))
  · have he := projectiveObservation_equal_times τ
      (P.sampledPathLaw_isProjectiveLimit hκ τ x) i j hij
    have hz : (fun q => (f (q j) - f (q i)) ^ 4) =ᵐ[P.sampledPathLaw hκ τ x] 0 :=
      he.mono (fun q hq => by simp [hq])
    calc
      _ = 0 := (integral_congr_ae hz).trans (by simp)
      _ ≤ _ := mul_nonneg hC0 (sq_nonneg _)
  · calc
      _ = ∫ q, (f (q i) - f (q j)) ^ 4 ∂P.sampledPathLaw hκ τ x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun q => by ring)
      _ ≤ C * (τ i - τ j).val ^ 2 :=
        P.sampledPathLaw_scalar_fourth_ordered hκ τ x f hC j i hij
      _ = _ := by rw [hd hij.le, dist_comm]

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_coordinate_fourth_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℕ → ℝ≥0) (x : GraphRealization P.geometry) (i j : ℕ),
      Integrable (fun q => (φ (P.geometry.smoothCoordinates (q j)) -
        φ (P.geometry.smoothCoordinates (q i))) ^ 4) (P.sampledPathLaw hκ τ x) ∧
      (∫ q, (φ (P.geometry.smoothCoordinates (q j)) -
        φ (P.geometry.smoothCoordinates (q i))) ^ 4 ∂P.sampledPathLaw hκ τ x) ≤
          C * dist (τ i) (τ j) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := P.coordinate_transition_fourth_bound hκ φ
  refine ⟨C, hC0, fun τ x i j => ⟨?_, ?_⟩⟩
  · exact P.sampledPathLaw_scalar_fourth_integrable hκ τ x (P.geometry.coordinateTest φ) i j
  · exact P.sampledPathLaw_scalar_fourth_bound hκ τ x (P.geometry.coordinateTest φ) hC0
      (fun T y => (hC T y).2) i j

end TimeTraps.Analysis
