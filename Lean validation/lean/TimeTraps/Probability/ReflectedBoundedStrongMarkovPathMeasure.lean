module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovPathData
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.Algebra.Group.Submonoid.Membership

@[expose] public section

/-! Finite Borel path measures are determined by continuous spatial
products at finitely many evaluation times. The separating algebra is
built explicitly, retaining repeated and unordered times. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction

def reflectedMarkovPathTest (L : ℝ) (H : ℝ≥0)
    (a : Icc (0 : ℝ≥0) H × C(Icc (0 : ℝ) L, ℝ)) : ReflectedMarkovPath L H →ᵇ ℝ :=
  (BoundedContinuousFunction.mkOfCompact a.2).compContinuous
    ⟨fun p => p a.1, continuous_eval_const a.1⟩

def reflectedMarkovPathProduct (L : ℝ) (H : ℝ≥0)
    (w : List (Icc (0 : ℝ≥0) H × C(Icc (0 : ℝ) L, ℝ))) : ReflectedMarkovPath L H →ᵇ ℝ :=
  (w.map (reflectedMarkovPathTest L H)).prod

def reflectedMarkovPathAlgebra (L : ℝ) (H : ℝ≥0) :
    StarSubalgebra ℝ (ReflectedMarkovPath L H →ᵇ ℝ) :=
  StarAlgebra.adjoin ℝ (range (reflectedMarkovPathTest L H))

theorem reflectedMarkovPathProduct_exists (L : ℝ) (H : ℝ≥0)
    {g : ReflectedMarkovPath L H →ᵇ ℝ}
    (hg : g ∈ Submonoid.closure (range (reflectedMarkovPathTest L H))) :
    ∃ w, reflectedMarkovPathProduct L H w = g := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
      rcases hg with ⟨a, rfl⟩
      exact ⟨[a], by simp [reflectedMarkovPathProduct]⟩
  | one => exact ⟨[], rfl⟩
  | mul g h _ _ hg hh =>
      rcases hg with ⟨v, rfl⟩
      rcases hh with ⟨w, rfl⟩
      exact ⟨v ++ w, by simp [reflectedMarkovPathProduct]⟩

theorem reflectedMarkovPathAlgebra_separates (L : ℝ) (H : ℝ≥0) :
    ((reflectedMarkovPathAlgebra L H).map
      (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro p q hpq
  have hn : ∃ t, p t ≠ q t := by
    by_contra! h
    exact hpq (ContinuousMap.ext h)
  rcases hn with ⟨t, ht⟩
  let f : C(Icc (0 : ℝ) L, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  let g := reflectedMarkovPathTest L H (t, f)
  refine ⟨g, ⟨g.toContinuousMap, ?_, rfl⟩, ?_⟩
  · exact StarSubalgebra.mem_map.mpr ⟨g,
      StarAlgebra.subset_adjoin ℝ _ (mem_range_self (t, f)), rfl⟩
  · exact fun he => ht (Subtype.ext he)

theorem reflectedMarkovPath_measure_ext (L : ℝ) (H : ℝ≥0)
    {μ ν : Measure (ReflectedMarkovPath L H)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (heq : ∀ w, ∫ p, reflectedMarkovPathProduct L H w p ∂μ =
      ∫ p, reflectedMarkovPathProduct L H w p ∂ν) : μ = ν := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish
    (reflectedMarkovPathAlgebra_separates L H)
  intro g hg
  let : TrivialStar (ReflectedMarkovPath L H →ᵇ ℝ) :=
    ⟨fun f => BoundedContinuousFunction.ext (fun p => star_trivial (f p))⟩
  have hspan : g ∈ Submodule.span ℝ
      (Submonoid.closure (range (reflectedMarkovPathTest L H)) : Set (ReflectedMarkovPath L H →ᵇ ℝ)) := by
    change g ∈ (reflectedMarkovPathAlgebra L H).toSubalgebra.toSubmodule at hg
    rw [reflectedMarkovPathAlgebra, StarAlgebra.adjoin_eq_span] at hg
    simpa only [star_trivial, union_self] using hg
  clear hg
  induction hspan using Submodule.span_induction with
  | mem g hg =>
      rcases reflectedMarkovPathProduct_exists L H hg with ⟨w, rfl⟩
      exact heq w
  | zero => simp
  | add f g _ _ hf hg =>
      change (∫ p, f p + g p ∂μ) = ∫ p, f p + g p ∂ν
      rw [integral_add (f.integrable μ) (g.integrable μ), integral_add (f.integrable ν) (g.integrable ν)]
      exact congrArg₂ (· + ·) hf hg
  | smul r f _ hf =>
      simpa only [BoundedContinuousFunction.smul_apply, smul_eq_mul, integral_const_mul] using
        congrArg (fun z : ℝ => r * z) hf

end TimeTraps.Probability

end
