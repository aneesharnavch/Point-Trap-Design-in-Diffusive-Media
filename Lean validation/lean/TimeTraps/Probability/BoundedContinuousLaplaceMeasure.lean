module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemLaplaceData
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.Algebra.Group.Submonoid.Membership

@[expose] public section

/-! Uniqueness of finite measures on nonnegative time from their Laplace
transforms. The exponential algebra is explicitly shown to separate points;
no Laplace injectivity or moment-determinacy assumption is imposed. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction

theorem nonnegativeLaplaceTest_bound (a t : ℝ≥0) :
    ‖Real.exp (-(a : ℝ) * (t : ℝ))‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr a.property) t.property)

def nonnegativeLaplaceTest (a : ℝ≥0) : ℝ≥0 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun t => Real.exp (-(a : ℝ) * (t : ℝ)), by fun_prop⟩ 2 (by
      intro s t
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans
        (by
          change ‖Real.exp (-(a : ℝ) * (s : ℝ))‖ + ‖Real.exp (-(a : ℝ) * (t : ℝ))‖ ≤ 2
          linarith [nonnegativeLaplaceTest_bound a s, nonnegativeLaplaceTest_bound a t]))

def nonnegativeLaplaceAlgebra : StarSubalgebra ℝ (ℝ≥0 →ᵇ ℝ) :=
  StarAlgebra.adjoin ℝ (range nonnegativeLaplaceTest)

theorem nonnegativeLaplaceTest_zero : nonnegativeLaplaceTest 0 = 1 := by
  ext t
  change Real.exp (-(0 : ℝ) * (t : ℝ)) = 1
  simp

theorem nonnegativeLaplaceTest_add (a b : ℝ≥0) :
    nonnegativeLaplaceTest (a + b) = nonnegativeLaplaceTest a * nonnegativeLaplaceTest b := by
  ext t
  change Real.exp (-((a + b : ℝ≥0) : ℝ) * (t : ℝ)) =
    Real.exp (-(a : ℝ) * (t : ℝ)) * Real.exp (-(b : ℝ) * (t : ℝ))
  rw [← Real.exp_add]
  congr 1
  simp only [NNReal.coe_add]
  ring

theorem nonnegativeLaplaceTest_closure {g : ℝ≥0 →ᵇ ℝ}
    (hg : g ∈ Submonoid.closure (range nonnegativeLaplaceTest)) :
    ∃ a, nonnegativeLaplaceTest a = g := by
  induction hg using Submonoid.closure_induction with
  | mem g hg => exact hg
  | one => exact ⟨0, nonnegativeLaplaceTest_zero⟩
  | mul g h _ _ hg hh =>
      rcases hg with ⟨a, rfl⟩
      rcases hh with ⟨b, rfl⟩
      exact ⟨a + b, nonnegativeLaplaceTest_add a b⟩

theorem nonnegativeLaplaceAlgebra_separates :
    (nonnegativeLaplaceAlgebra.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro s t hst
  let g := nonnegativeLaplaceTest 1
  refine ⟨g, ⟨g.toContinuousMap, ?_, rfl⟩, ?_⟩
  · exact StarSubalgebra.mem_map.mpr ⟨g,
      StarAlgebra.subset_adjoin ℝ _ (mem_range_self 1), rfl⟩
  · intro he
    have he' : Real.exp (-(s : ℝ)) = Real.exp (-(t : ℝ)) := by
      simpa only [g, nonnegativeLaplaceTest, BoundedContinuousFunction.mkOfBound_coe,
        ContinuousMap.coe_mk, NNReal.coe_one, neg_one_mul] using he
    exact hst (Subtype.ext (neg_injective (Real.exp_injective he')))

theorem nonnegativeLaplace_measure_ext {μ ν : Measure ℝ≥0}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (heq : ∀ a : ℝ≥0,
      (∫ t, Real.exp (-(a : ℝ) * (t : ℝ)) ∂μ) =
        ∫ t, Real.exp (-(a : ℝ) * (t : ℝ)) ∂ν) : μ = ν := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish nonnegativeLaplaceAlgebra_separates
  intro g hg
  let : TrivialStar (ℝ≥0 →ᵇ ℝ) :=
    ⟨fun f => BoundedContinuousFunction.ext (fun t => star_trivial (f t))⟩
  have hspan : g ∈ Submodule.span ℝ
      (Submonoid.closure (range nonnegativeLaplaceTest) : Set (ℝ≥0 →ᵇ ℝ)) := by
    change g ∈ nonnegativeLaplaceAlgebra.toSubalgebra.toSubmodule at hg
    rw [nonnegativeLaplaceAlgebra, StarAlgebra.adjoin_eq_span] at hg
    simpa only [star_trivial, union_self] using hg
  clear hg
  induction hspan using Submodule.span_induction with
  | mem g hg =>
      rcases nonnegativeLaplaceTest_closure hg with ⟨a, rfl⟩
      exact heq a
  | zero => simp
  | add f g _ _ hf hg =>
      change (∫ t, f t + g t ∂μ) = ∫ t, f t + g t ∂ν
      rw [integral_add (f.integrable μ) (g.integrable μ), integral_add (f.integrable ν) (g.integrable ν)]
      exact congrArg₂ (· + ·) hf hg
  | smul r f _ hf =>
      simpa only [BoundedContinuousFunction.smul_apply, smul_eq_mul, integral_const_mul] using
        congrArg (fun z : ℝ => r * z) hf

end TimeTraps.Probability

end
