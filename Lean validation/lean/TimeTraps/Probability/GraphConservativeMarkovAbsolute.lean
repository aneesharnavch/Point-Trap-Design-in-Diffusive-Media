module

public import TimeTraps.Probability.GraphConservativeMarkovWord
public import TimeTraps.Probability.GraphConservativeContinuousMarginal
public import Mathlib.Data.List.Sort

@[expose] public section

/-! Arbitrary finite continuous products, including repeated and unordered
times, are sorted into the proved chronological stopping-time identity. -/

noncomputable section
namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E]

def graphMarkovAbsoluteCylinder (G : MetricGraph V E) (w : GraphMarkovWord G)
    (t : ℝ≥0) (p : GraphContinuousPath G) : ℝ :=
  (w.map (fun a => a.2 (p (t + a.1)))).prod

def graphMarkovDurations {G : MetricGraph V E} : ℝ≥0 → GraphMarkovWord G → GraphMarkovWord G
  | _, [] => []
  | s, (t, f) :: w => (t - s, f) :: graphMarkovDurations t w

def graphMarkovTimeSort {G : MetricGraph V E} (w : GraphMarkovWord G) : GraphMarkovWord G :=
  w.mergeSort (fun a b => a.1 ≤ b.1)

omit [Fintype V] [Fintype E] in
theorem graphMarkovTimeSort_pairwise {G : MetricGraph V E} (w : GraphMarkovWord G) :
    (graphMarkovTimeSort w).Pairwise (fun a b => a.1 ≤ b.1) := by
  simpa only [graphMarkovTimeSort, decide_eq_true_eq] using
    (List.pairwise_mergeSort (le := fun a b : ℝ≥0 × C(GraphRealization G, ℝ) => a.1 ≤ b.1)
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hab hbc)
      (fun a b => by simpa using le_total a.1 b.1) w)

omit [Fintype V] [Fintype E] in
theorem graphMarkovDurations_cylinder (G : MetricGraph V E) (w : GraphMarkovWord G) (s : ℝ≥0)
    (hw : w.Pairwise (fun a b => a.1 ≤ b.1)) (hs : ∀ a ∈ w, s ≤ a.1)
    (t : ℝ≥0) (p : GraphContinuousPath G) :
    graphMarkovCylinder G (graphMarkovDurations s w) (t + s) p =
      graphMarkovAbsoluteCylinder G w t p := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
      rcases a with ⟨r, f⟩
      have hsr : s ≤ r := hs _ List.mem_cons_self
      have hsum : t + s + (r - s) = t + r := by rw [add_assoc, add_tsub_cancel_of_le hsr]
      simp only [graphMarkovDurations, graphMarkovCylinder, hsum]
      rw [ih r hw.tail (List.pairwise_cons.mp hw).1]
      rfl

omit [Fintype V] [Fintype E] in
theorem graphMarkovAbsoluteCylinder_sorted (G : MetricGraph V E)
    (w : GraphMarkovWord G) (t : ℝ≥0) (p : GraphContinuousPath G) :
    graphMarkovAbsoluteCylinder G w t p =
      graphMarkovCylinder G (graphMarkovDurations 0 (graphMarkovTimeSort w)) t p := by
  have he := graphMarkovDurations_cylinder G (graphMarkovTimeSort w) 0
    (graphMarkovTimeSort_pairwise w) (fun _ _ => bot_le) t p
  simp only [add_zero] at he
  rw [he]
  exact ((List.mergeSort_perm w (fun a b => a.1 ≤ b.1)).map
    (fun a => a.2 (p (t + a.1)))).prod_eq.symm

def GraphShiftedContactOperatorProblem.markovAbsoluteKernel [Nonempty E]
    (P : GraphShiftedContactOperatorProblem V E) (w : GraphMarkovWord P.geometry) :
    C(GraphRealization P.geometry, ℝ) :=
  P.markovCylinderKernel (graphMarkovDurations 0 (graphMarkovTimeSort w))

theorem GraphShiftedContactOperatorProblem.markovAbsoluteCylinder_integrable [Nonempty E]
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (w : GraphMarkovWord P.geometry)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0))) :
    Integrable (fun p => graphMarkovAbsoluteCylinder P.geometry w (τ p) p) (P.continuousPathLaw hκ x) := by
  simpa only [graphMarkovAbsoluteCylinder_sorted] using
    P.markovCylinder_stopped_integrable hκ x (graphMarkovDurations 0 (graphMarkovTimeSort w)) hτ

theorem GraphShiftedContactOperatorProblem.markovAbsoluteCylinder_condExp [Nonempty E]
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (w : GraphMarkovWord P.geometry)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0))) :
    (P.continuousPathLaw hκ x)[(fun p => graphMarkovAbsoluteCylinder P.geometry w (τ p) p) |
      hτ.measurableSpace] =ᵐ[P.continuousPathLaw hκ x]
        (fun p => P.markovAbsoluteKernel w (p (τ p))) := by
  simpa only [graphMarkovAbsoluteCylinder_sorted, GraphShiftedContactOperatorProblem.markovAbsoluteKernel] using
    P.markovCylinder_condExp hκ x (graphMarkovDurations 0 (graphMarkovTimeSort w)) hτ

theorem GraphShiftedContactOperatorProblem.markovAbsoluteCylinder_expectation [Nonempty E]
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (y : GraphRealization P.geometry) (w : GraphMarkovWord P.geometry) :
    (∫ p, graphMarkovAbsoluteCylinder P.geometry w 0 p ∂P.continuousPathLaw hκ y) =
      P.markovAbsoluteKernel w y := by
  let inst := P.continuousPathLaw_probability hκ y
  have hτ := isStoppingTime_const (graphContinuousNaturalFiltration P.geometry) (0 : ℝ≥0)
  have he := P.markovAbsoluteCylinder_condExp hκ y w hτ
  calc
    _ = ∫ p, P.markovAbsoluteKernel w (p 0) ∂P.continuousPathLaw hκ y := by
      rw [← integral_condExp hτ.measurableSpace_le]
      exact integral_congr_ae he
    _ = ∫ _, P.markovAbsoluteKernel w y ∂P.continuousPathLaw hκ y := by
      exact integral_congr_ae ((P.continuousPathLaw_initial hκ y).mono
        (fun p hp => congrArg (P.markovAbsoluteKernel w) hp))
    _ = _ := by simp

end TimeTraps.Analysis
end
