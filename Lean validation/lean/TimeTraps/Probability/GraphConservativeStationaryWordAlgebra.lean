module

public import TimeTraps.Probability.GraphConservativeStationaryPairing
public import TimeTraps.Probability.GraphConservativeMarkovWordData

@[expose] public section

/-! Reversing a word of self-adjoint operators reverses a stationary
pairing. Graph heat steps and multiplication by continuous observations
are the actual operators, with no reverse-path law assumed. -/

namespace TimeTraps.Probability

open MeasureTheory

variable {X I : Type*} [TopologicalSpace X] [MeasurableSpace X]

theorem integral_operatorWord_reverse (μ : Measure X) (A : I → C(X, ℝ) → C(X, ℝ))
    (hA : ∀ i f g, (∫ x, f x * A i g x ∂μ) = ∫ x, g x * A i f x ∂μ)
    (w : List I) (f g : C(X, ℝ)) :
    (∫ x, f x * (w.foldr A g) x ∂μ) =
      ∫ x, g x * (w.reverse.foldr A f) x ∂μ := by
  induction w generalizing f with
  | nil =>
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
  | cons i w ih =>
    calc
      _ = ∫ x, (w.foldr A g) x * A i f x ∂μ := hA i f (w.foldr A g)
      _ = ∫ x, A i f x * (w.foldr A g) x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
      _ = ∫ x, g x * (w.reverse.foldr A (A i f)) x ∂μ := ih (A i f)
      _ = _ := by simp only [List.reverse_cons, List.foldr_append, List.foldr_cons, List.foldr_nil]

end TimeTraps.Probability

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

abbrev GraphHeatWordLetter (G : MetricGraph V E) := ℝ≥0 ⊕ C(GraphRealization G, ℝ)

noncomputable def GraphShiftedContactOperatorProblem.heatWordAction
    (P : GraphShiftedContactOperatorProblem V E) :
    GraphHeatWordLetter P.geometry → C(GraphRealization P.geometry, ℝ) → C(GraphRealization P.geometry, ℝ)
  | .inl t, f => P.realizedFeller t f
  | .inr g, f => g * f

noncomputable def GraphShiftedContactOperatorProblem.heatWordApply
    (P : GraphShiftedContactOperatorProblem V E) (w : List (GraphHeatWordLetter P.geometry))
    (f : C(GraphRealization P.geometry, ℝ)) : C(GraphRealization P.geometry, ℝ) :=
  w.foldr P.heatWordAction f

def graphHeatWordLetters {G : MetricGraph V E} (w : GraphMarkovWord G) : List (GraphHeatWordLetter G) :=
  w.flatMap (fun a => [.inl a.1, .inr a.2])

theorem GraphShiftedContactOperatorProblem.heatWordApply_append
    (P : GraphShiftedContactOperatorProblem V E) (w z : List (GraphHeatWordLetter P.geometry))
    (f : C(GraphRealization P.geometry, ℝ)) :
    P.heatWordApply (w ++ z) f = P.heatWordApply w (P.heatWordApply z f) :=
  List.foldr_append

theorem GraphShiftedContactOperatorProblem.heatWordApply_reverse
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (w : List (GraphHeatWordLetter P.geometry)) (f g : C(GraphRealization P.geometry, ℝ)) :
    (∫ x, f x * P.heatWordApply w g x ∂P.geometry.lengthMeasure) =
      ∫ x, g x * P.heatWordApply w.reverse f x ∂P.geometry.lengthMeasure := by
  apply integral_operatorWord_reverse
  intro i u v
  cases i with
  | inl t => exact P.realizedFeller_length_pairing h0 t u v
  | inr k =>
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    change u x * (k x * v x) = v x * (k x * u x)
    ring

theorem GraphShiftedContactOperatorProblem.heatWordLetters_apply_one
    (P : GraphShiftedContactOperatorProblem V E) (w : GraphMarkovWord P.geometry) :
    P.heatWordApply (graphHeatWordLetters w) 1 = P.markovCylinderKernel w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨t, f⟩
    change P.realizedFeller t (f * P.heatWordApply (graphHeatWordLetters w) 1) =
      P.realizedFeller t (f * P.markovCylinderKernel w)
    rw [ih]

end TimeTraps.Analysis
