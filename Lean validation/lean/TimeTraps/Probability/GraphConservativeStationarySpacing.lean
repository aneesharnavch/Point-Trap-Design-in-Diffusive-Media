module

public import TimeTraps.Probability.GraphConservativeStationaryWordAlgebra
public import TimeTraps.Probability.GraphConservativeMarkovAbsolute

@[expose] public section

/-! An observation word with an explicit terminal heat step has an
exact reversed letter list. Truncated nonnegative-time subtraction is
retained, including repeated observation times and empty words. -/

namespace TimeTraps.Analysis

open TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E]

def graphMarkovSpacedLetters {G : MetricGraph V E} :
    ℝ≥0 → ℝ≥0 → GraphMarkovWord G → List (GraphHeatWordLetter G)
  | s, T, [] => [.inl (T - s)]
  | s, T, (t, f) :: w => .inl (t - s) :: .inr f :: graphMarkovSpacedLetters t T w

omit [Fintype V] [Fintype E] in
theorem graphMarkovSpacedLetters_snoc {G : MetricGraph V E} (w : GraphMarkovWord G)
    (s T t : ℝ≥0) (f : C(GraphRealization G, ℝ)) :
    graphMarkovSpacedLetters s T (w ++ [(t, f)]) =
      graphMarkovSpacedLetters s t w ++ [.inr f, .inl (T - t)] := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
      rcases a with ⟨r, g⟩
      simp only [List.cons_append, graphMarkovSpacedLetters, ih]

omit [Fintype V] [Fintype E] in
theorem graphMarkovSpacedLetters_reverse_general {G : MetricGraph V E}
    (w : GraphMarkovWord G) (s T B : ℝ≥0) (hT : T ≤ B)
    (hw : ∀ a ∈ w, a.1 ≤ B) :
    (graphMarkovSpacedLetters s T w).reverse =
      graphMarkovSpacedLetters (B - T) (B - s)
        (w.reverse.map (fun a => (B - a.1, a.2))) := by
  induction w generalizing s with
  | nil =>
      simp only [graphMarkovSpacedLetters, List.reverse_singleton, List.reverse_nil, List.map_nil,
        tsub_tsub_tsub_cancel_left hT]
  | cons a w ih =>
      rcases a with ⟨r, f⟩
      have hr : r ≤ B := hw _ List.mem_cons_self
      have htail : ∀ a ∈ w, a.1 ≤ B := fun a ha => hw a (List.mem_cons_of_mem _ ha)
      simp only [graphMarkovSpacedLetters, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      rw [ih r htail, graphMarkovSpacedLetters_snoc, tsub_tsub_tsub_cancel_left hr]
      simp only [List.append_assoc, List.singleton_append]

omit [Fintype V] [Fintype E] in
theorem graphMarkovSpacedLetters_reverse {G : MetricGraph V E}
    (w : GraphMarkovWord G) (T : ℝ≥0) (hw : ∀ a ∈ w, a.1 ≤ T) :
    (graphMarkovSpacedLetters 0 T w).reverse =
      graphMarkovSpacedLetters 0 T (w.reverse.map (fun a => (T - a.1, a.2))) := by
  simpa only [tsub_self, tsub_zero] using
    graphMarkovSpacedLetters_reverse_general w 0 T T le_rfl hw

end TimeTraps.Analysis
