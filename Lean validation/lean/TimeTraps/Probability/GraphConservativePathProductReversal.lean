module

public import TimeTraps.Probability.GraphConservativeFuturePathMeasure
public import TimeTraps.Probability.GraphConservativeMarkovAbsolute
public import TimeTraps.Probability.GraphContinuousPathReversal

@[expose] public section

/-! Finite path tests under stopping and reversal are transported to
chronological words in the same compact time window. Repeated times and
observations beyond the horizon are retained by literal clamping. -/

noncomputable section

namespace TimeTraps.Analysis

open TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem graphMarkovPathProduct_eq_absolute (G : MetricGraph V E)
    (w : GraphMarkovWord G) (p : GraphContinuousPath G) :
    graphMarkovPathProduct G w p = graphMarkovAbsoluteCylinder G w 0 p := by
  induction w with
  | nil => simp [graphMarkovPathProduct, graphMarkovAbsoluteCylinder]
  | cons a w ih =>
    simpa [graphMarkovPathProduct, graphMarkovAbsoluteCylinder, graphMarkovPathTest] using
      congrArg (fun r : ℝ => a.2 (p a.1) * r) ih

omit [Fintype V] [Fintype E] in
theorem graphMarkovAbsoluteCylinder_perm (G : MetricGraph V E)
    {w z : GraphMarkovWord G} (h : w.Perm z) (t : ℝ≥0) (p : GraphContinuousPath G) :
    graphMarkovAbsoluteCylinder G w t p = graphMarkovAbsoluteCylinder G z t p := by
  unfold graphMarkovAbsoluteCylinder
  exact (h.map (fun a => a.2 (p (t + a.1)))).prod_eq

def graphMarkovWindowWord {G : MetricGraph V E} (T : ℝ≥0) (w : GraphMarkovWord G) :
    GraphMarkovWord G := graphMarkovTimeSort (w.map (fun a => (min a.1 T, a.2)))

omit [Fintype V] [Fintype E] in
theorem graphMarkovWindowWord_pairwise {G : MetricGraph V E}
    (T : ℝ≥0) (w : GraphMarkovWord G) :
    (graphMarkovWindowWord T w).Pairwise (fun a b => a.1 ≤ b.1) :=
  graphMarkovTimeSort_pairwise _

omit [Fintype V] [Fintype E] in
theorem graphMarkovWindowWord_le {G : MetricGraph V E}
    (T : ℝ≥0) (w : GraphMarkovWord G) : ∀ a ∈ graphMarkovWindowWord T w, a.1 ≤ T := by
  intro a ha
  change a ∈ (w.map (fun a => (min a.1 T, a.2))).mergeSort (fun a b => a.1 ≤ b.1) at ha
  have hm : a ∈ w.map (fun a => (min a.1 T, a.2)) :=
    (List.mergeSort_perm _ (fun a b => a.1 ≤ b.1)).mem_iff.mp ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hm
  exact min_le_right _ _

omit [Fintype V] in
theorem graphMarkovPathProduct_stop (G : MetricGraph V E)
    (T : ℝ≥0) (w : GraphMarkovWord G) (p : GraphContinuousPath G) :
    graphMarkovPathProduct G w (graphContinuousPathStop G T p) =
      graphMarkovAbsoluteCylinder G (graphMarkovWindowWord T w) 0 p := by
  rw [graphMarkovPathProduct_eq_absolute]
  calc
    _ = graphMarkovAbsoluteCylinder G (w.map (fun a => (min a.1 T, a.2))) 0 p := by
      simp only [graphMarkovAbsoluteCylinder, List.map_map, Function.comp_def, zero_add,
        graphContinuousPathStop_apply]
    _ = _ := graphMarkovAbsoluteCylinder_perm G (List.mergeSort_perm _ _).symm 0 p

omit [Fintype V] in
theorem graphMarkovPathProduct_reverse (G : MetricGraph V E)
    (T : ℝ≥0) (w : GraphMarkovWord G) (p : GraphContinuousPath G) :
    graphMarkovPathProduct G w (graphContinuousPathReverse G T p) =
      graphMarkovAbsoluteCylinder G
        ((graphMarkovWindowWord T w).reverse.map (fun a => (T - a.1, a.2))) 0 p := by
  have hsub (t : ℝ≥0) : T - min t T = T - t := by
    rcases le_total t T with ht | ht
    · rw [min_eq_left ht]
    · rw [min_eq_right ht, tsub_self, tsub_eq_zero_of_le ht]
  have hs : (graphMarkovWindowWord T w).Perm (w.map (fun a => (min a.1 T, a.2))) :=
    List.mergeSort_perm _ _
  have hp : (w.map (fun a => (min a.1 T, a.2))).reverse.Perm (graphMarkovWindowWord T w).reverse :=
    (List.reverse_perm _).trans (hs.symm.trans (List.reverse_perm _).symm)
  rw [graphMarkovPathProduct_eq_absolute]
  calc
    _ = graphMarkovAbsoluteCylinder G
        ((w.map (fun a => (min a.1 T, a.2))).reverse.map (fun a => (T - a.1, a.2))) 0 p := by
      simp only [graphMarkovAbsoluteCylinder, List.map_map, List.map_reverse, Function.comp_def,
        List.prod_reverse, zero_add, graphContinuousPathReverse_apply, hsub]
    _ = _ := graphMarkovAbsoluteCylinder_perm G
      (hp.map (fun a => (T - a.1, a.2))) 0 p

end TimeTraps.Analysis

end
