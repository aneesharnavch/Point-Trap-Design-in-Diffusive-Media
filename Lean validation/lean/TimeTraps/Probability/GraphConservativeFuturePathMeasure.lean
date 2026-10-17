module

public import TimeTraps.Probability.GraphConservativeFuturePathData
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.Algebra.Group.Submonoid.Membership

@[expose] public section

/-! Finite Borel path measures are determined by continuous spatial
products at finitely many evaluation times. The separating algebra is
built explicitly, retaining repeated and unordered times. -/

noncomputable section

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal BoundedContinuousFunction

variable {V E : Type*} [Fintype V] [Fintype E]

def graphMarkovPathTest (G : MetricGraph V E)
    (a : ℝ≥0 × C(GraphRealization G, ℝ)) : GraphContinuousPath G →ᵇ ℝ :=
  (BoundedContinuousFunction.mkOfCompact a.2).compContinuous
    ⟨fun p => p a.1, continuous_eval_const a.1⟩

def graphMarkovPathProduct (G : MetricGraph V E)
    (w : List (ℝ≥0 × C(GraphRealization G, ℝ))) : GraphContinuousPath G →ᵇ ℝ :=
  (w.map (graphMarkovPathTest G)).prod

def graphMarkovPathAlgebra (G : MetricGraph V E) :
    StarSubalgebra ℝ (GraphContinuousPath G →ᵇ ℝ) :=
  StarAlgebra.adjoin ℝ (range (graphMarkovPathTest G))

omit [Fintype V] in
theorem graphMarkovPathProduct_exists (G : MetricGraph V E)
    {g : GraphContinuousPath G →ᵇ ℝ}
    (hg : g ∈ Submonoid.closure (range (graphMarkovPathTest G))) :
    ∃ w, graphMarkovPathProduct G w = g := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
      rcases hg with ⟨a, rfl⟩
      exact ⟨[a], by simp [graphMarkovPathProduct]⟩
  | one => exact ⟨[], rfl⟩
  | mul g h _ _ hg hh =>
      rcases hg with ⟨v, rfl⟩
      rcases hh with ⟨w, rfl⟩
      exact ⟨v ++ w, by simp [graphMarkovPathProduct]⟩

theorem graphMarkovPathAlgebra_separates (G : MetricGraph V E) :
    ((graphMarkovPathAlgebra G).map
      (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro p q hpq
  have hn : ∃ t, p t ≠ q t := by
    by_contra! h
    exact hpq (ContinuousMap.ext h)
  rcases hn with ⟨t, ht⟩
  let f : C(GraphRealization G, ℝ) := ⟨fun z => dist z (p t), continuous_id.dist continuous_const⟩
  let g := graphMarkovPathTest G (t, f)
  refine ⟨g, ⟨g.toContinuousMap, ?_, rfl⟩, ?_⟩
  · exact StarSubalgebra.mem_map.mpr ⟨g,
      StarAlgebra.subset_adjoin ℝ _ (mem_range_self (t, f)), rfl⟩
  · intro he
    have hz : dist (q t) (p t) = 0 := by
      change dist (p t) (p t) = dist (q t) (p t) at he
      simpa only [dist_self] using he.symm
    exact ht (dist_eq_zero.mp hz).symm

theorem graphMarkovPath_measure_ext (G : MetricGraph V E)
    {μ ν : Measure (GraphContinuousPath G)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (heq : ∀ w, ∫ p, graphMarkovPathProduct G w p ∂μ =
      ∫ p, graphMarkovPathProduct G w p ∂ν) : μ = ν := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish
    (graphMarkovPathAlgebra_separates G)
  intro g hg
  let : TrivialStar (GraphContinuousPath G →ᵇ ℝ) :=
    ⟨fun f => BoundedContinuousFunction.ext (fun p => star_trivial (f p))⟩
  have hspan : g ∈ Submodule.span ℝ
      (Submonoid.closure (range (graphMarkovPathTest G)) : Set (GraphContinuousPath G →ᵇ ℝ)) := by
    change g ∈ (graphMarkovPathAlgebra G).toSubalgebra.toSubmodule at hg
    rw [graphMarkovPathAlgebra, StarAlgebra.adjoin_eq_span] at hg
    simpa only [star_trivial, union_self] using hg
  clear hg
  induction hspan using Submodule.span_induction with
  | mem g hg =>
      rcases graphMarkovPathProduct_exists G hg with ⟨w, rfl⟩
      exact heq w
  | zero => simp
  | add f g _ _ hf hg =>
      change (∫ p, f p + g p ∂μ) = ∫ p, f p + g p ∂ν
      rw [integral_add (f.integrable μ) (g.integrable μ), integral_add (f.integrable ν) (g.integrable ν)]
      exact congrArg₂ (· + ·) hf hg
  | smul r f _ hf =>
      simpa only [BoundedContinuousFunction.smul_apply, smul_eq_mul, integral_const_mul] using
        congrArg (fun z : ℝ => r * z) hf

end TimeTraps.Analysis

end
