module

public import TimeTraps.Probability.GraphOccupationCompactMeasurable

@[expose] public section

/-! Actual L2 classes of the uniform-norm compact occupation paths under
the constructed graph path law. The square integrability follows from
the deterministic pathwise bound, without a maximal estimate premise. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupationCompact_memLp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    MemLp (graphOccupationCompactPath P.geometry f T) 2 (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact MemLp.of_bound (graphOccupationCompactPath_stronglyMeasurable P.geometry f T).aestronglyMeasurable
    ((T : ℝ) * ‖f‖) (Eventually.of_forall (graphOccupationCompactPath_norm_le P.geometry f T))

noncomputable def GraphShiftedContactOperatorProblem.occupationCompactL2
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    Lp C(Icc (0 : ℝ≥0) T, ℝ) 2 (P.continuousPathLaw hκ x) :=
  (P.occupationCompact_memLp hκ x f T).toLp (graphOccupationCompactPath P.geometry f T)

theorem GraphShiftedContactOperatorProblem.occupationCompactL2_coe
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    P.occupationCompactL2 hκ x f T =ᵐ[P.continuousPathLaw hκ x] graphOccupationCompactPath P.geometry f T :=
  (P.occupationCompact_memLp hκ x f T).coeFn_toLp

theorem GraphShiftedContactOperatorProblem.occupationCompactL2_eval_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ t : Icc (0 : ℝ≥0) T,
      (P.occupationCompactL2 hκ x f T p) t = graphOccupation P.geometry f t.val p := by
  filter_upwards [P.occupationCompactL2_coe hκ x f T] with p hp
  intro t
  exact congrArg (fun q : C(Icc (0 : ℝ≥0) T, ℝ) => q t) hp

theorem GraphShiftedContactOperatorProblem.occupationCompactL2_norm_sq
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    ‖P.occupationCompactL2 hκ x f T‖ ^ 2 =
      ∫ p, ‖graphOccupationCompactPath P.geometry f T p‖ ^ 2 ∂P.continuousPathLaw hκ x := by
  let h := P.occupationCompact_memLp hκ x f T
  have he : ‖h.toLp (graphOccupationCompactPath P.geometry f T)‖ =
      ‖h.norm.toLp (fun p => ‖graphOccupationCompactPath P.geometry f T p‖)‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm]
  change ‖h.toLp (graphOccupationCompactPath P.geometry f T)‖ ^ 2 = _
  rw [he, memLp_norm_toLp_sq]

end TimeTraps.Analysis
