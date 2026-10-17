module

public import TimeTraps.Analysis.GraphConservativeMomentPairSampled
public import TimeTraps.Analysis.GraphConservativeMomentCoordinate
public import TimeTraps.Probability.ProjectiveObservationEqualTimes

@[expose] public section

/-! The actual sampled conservative graph law has the expected ordered
pair transition, and all continuous scalar increments have genuine
fourth integrability before their expectations are estimated. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_pair_map
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (τ : ℕ → ℝ≥0) (x : GraphRealization P.geometry) (i j : ℕ) (hij : τ i < τ j) :
    (P.sampledPathLaw hκ τ x).map (fun q => (q i, q j)) =
      (P.realizedTransition (τ i) x) ⊗ₘ P.realizedTransition (τ j - τ i) := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) :=
    fun t => P.realizedTransition_isMarkov hκ t
  exact projectiveMarkov_pair_map P.realizedTransition τ x
    (P.sampledPathLaw_isProjectiveLimit hκ τ x) i j hij

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_scalar_fourth_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (τ : ℕ → ℝ≥0) (x : GraphRealization P.geometry)
    (f : C(GraphRealization P.geometry, ℝ)) (i j : ℕ) :
    Integrable (fun q => (f (q j) - f (q i)) ^ 4) (P.sampledPathLaw hκ τ x) := by
  let inst := P.sampledPathLaw_probability hκ τ x
  exact ((f.continuous.comp (continuous_apply j)).sub
    (f.continuous.comp (continuous_apply i))).pow 4 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_scalar_fourth_ordered
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (τ : ℕ → ℝ≥0) (x : GraphRealization P.geometry)
    (f : C(GraphRealization P.geometry, ℝ)) {C : ℝ}
    (hC : ∀ (T : ℝ≥0) (y : GraphRealization P.geometry),
      (∫ z, (f z - f y) ^ 4 ∂P.realizedTransition T y) ≤ C * T.val ^ 2)
    (i j : ℕ) (hij : τ i < τ j) :
    (∫ q, (f (q j) - f (q i)) ^ 4 ∂P.sampledPathLaw hκ τ x) ≤
      C * (τ j - τ i).val ^ 2 := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) :=
    fun t => P.realizedTransition_isMarkov hκ t
  let F : GraphRealization P.geometry × GraphRealization P.geometry → ℝ :=
    fun p => (f p.2 - f p.1) ^ 4
  have hF : Continuous F := ((f.continuous.comp continuous_snd).sub
    (f.continuous.comp continuous_fst)).pow 4
  have hi : Integrable F ((P.realizedTransition (τ i) x) ⊗ₘ P.realizedTransition (τ j - τ i)) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi |>.2
  have hn' : Integrable (fun y => ∫ z, (f z - f y) ^ 4
      ∂P.realizedTransition (τ j - τ i) y) (P.realizedTransition (τ i) x) := by
    simpa only [F, Real.norm_eq_abs, abs_pow, (show Even 4 from by decide).pow_abs] using hn
  calc
    _ = ∫ p, F p ∂((P.sampledPathLaw hκ τ x).map (fun q => (q i, q j))) :=
      (integral_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
        hF.aestronglyMeasurable).symm
    _ = ∫ p, F p ∂((P.realizedTransition (τ i) x) ⊗ₘ P.realizedTransition (τ j - τ i)) :=
      congrArg (fun μ => ∫ p, F p ∂μ) (P.sampledPathLaw_pair_map hκ τ x i j hij)
    _ = ∫ y, ∫ z, (f z - f y) ^ 4 ∂P.realizedTransition (τ j - τ i) y
        ∂P.realizedTransition (τ i) x := Measure.integral_compProd hi
    _ ≤ ∫ _, C * (τ j - τ i).val ^ 2 ∂P.realizedTransition (τ i) x :=
      integral_mono hn' (integrable_const _) (hC (τ j - τ i))
    _ = _ := by simp

end TimeTraps.Analysis
