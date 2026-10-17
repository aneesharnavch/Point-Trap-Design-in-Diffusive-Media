module

public import TimeTraps.Probability.ReflectedNeumannCosine

@[expose] public section

/-! Identification of the actual reflected L2 generator with the negative
of the actual empty-contact Neumann operator. Finite cosine graph pairs
converge in both components, so closedness proves the forward direction.
The actual self-adjoint graph gives the converse coefficient identity. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped Topology

theorem reflectedPhysical_generator_mem_neumann_graph (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) {f g : ReflectedUniformL2 L hL}
    (hg : HasDerivWithinAt (reflectedGaussianPhysicalL2Curve L hL D f) g (Ici 0) 0) :
    (reflectedUniformL2Equiv L hL f, -reflectedUniformL2Equiv L hL g) ∈
      (reflectedNeumannProblem L hL D hD).operator.graph := by
  have hf : HasSum (fun n : ℕ => inner ℝ (reflectedCosineHilbertBasis L hL n) f •
      reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n))
      (reflectedUniformL2Equiv L hL f) := by
    simpa only [ContinuousLinearEquiv.coe_coe, HilbertBasis.repr_apply_apply, map_smul] using
      ((reflectedCosineHilbertBasis L hL).hasSum_repr f).mapL
        (reflectedUniformL2Equiv L hL).toContinuousLinearMap
  have hh : HasSum (fun n : ℕ =>
      (reflectedCosinePhysicalRate L D n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) •
        reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n))
      (-reflectedUniformL2Equiv L hL g) := by
    simpa only [ContinuousLinearEquiv.coe_coe, map_smul, map_neg, neg_mul, neg_smul, neg_neg] using
      ((reflectedGaussianPhysicalL2Curve_generator_hasSum L hL hD hg).mapL
        (reflectedUniformL2Equiv L hL).toContinuousLinearMap).neg
  have hclosed : IsClosed ((reflectedNeumannProblem L hL D hD).operator.graph :
      Set (IntervalSobolevL2 0 L × IntervalSobolevL2 0 L)) :=
    (reflectedNeumannProblem L hL D hD).operator_closed
  apply hclosed.mem_of_tendsto (hf.prodMk hh)
  apply Filter.Eventually.of_forall
  intro s
  change (∑ n ∈ s, (inner ℝ (reflectedCosineHilbertBasis L hL n) f •
      reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n),
    (reflectedCosinePhysicalRate L D n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) •
      reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n))) ∈
        (reflectedNeumannProblem L hL D hD).operator.graph
  simpa only [prod_mk_sum] using
    reflectedNeumann_finite_cosine_graph L hL D hD s
      (fun n => inner ℝ (reflectedCosineHilbertBasis L hL n) f)

theorem reflectedNeumann_graph_generator_coefficients (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) {f g : ReflectedUniformL2 L hL}
    (hg : (reflectedUniformL2Equiv L hL f, -reflectedUniformL2Equiv L hL g) ∈
      (reflectedNeumannProblem L hL D hD).operator.graph) (n : ℕ) :
    inner ℝ (reflectedCosineHilbertBasis L hL n) g =
      -reflectedCosinePhysicalRate L D n * inner ℝ (reflectedCosineHilbertBasis L hL n) f := by
  have ha : (reflectedUniformL2Equiv L hL f, -reflectedUniformL2Equiv L hL g) ∈
      (reflectedNeumannProblem L hL D hD).operator.graph.adjoint := by
    rw [← LinearPMap.adjoint_graph_eq_graph_adjoint
      (reflectedNeumannProblem L hL D hD).operator_dense_domain,
      LinearPMap.isSelfAdjoint_def.mp (reflectedNeumannProblem L hL D hD).operator_selfAdjoint]
    exact hg
  have he := (Submodule.mem_adjoint_iff _ _).mp ha
    (reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n))
    (reflectedCosinePhysicalRate L D n •
      reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n))
    (reflectedNeumann_cosine_graph L hL D hD n)
  change inner ℝ (reflectedCosinePhysicalRate L D n •
      reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n))
      (reflectedUniformL2Equiv L hL f) -
    inner ℝ (reflectedUniformL2Equiv L hL (reflectedCosineHilbertBasis L hL n))
      (-reflectedUniformL2Equiv L hL g) = 0 at he
  rw [real_inner_smul_left, inner_neg_right, reflectedUniformL2Equiv_inner,
    reflectedUniformL2Equiv_inner] at he
  have hz : L * (inner ℝ (reflectedCosineHilbertBasis L hL n) g +
      reflectedCosinePhysicalRate L D n * inner ℝ (reflectedCosineHilbertBasis L hL n) f) = 0 := by
    nlinarith [he]
  have hz' := (mul_eq_zero.mp hz).resolve_left hL.ne'
  linarith

theorem reflectedPhysical_generator_iff_neumann_graph (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f g : ReflectedUniformL2 L hL) :
    HasDerivWithinAt (reflectedGaussianPhysicalL2Curve L hL D f) g (Ici 0) 0 ↔
      (reflectedUniformL2Equiv L hL f, -reflectedUniformL2Equiv L hL g) ∈
        (reflectedNeumannProblem L hL D hD).operator.graph := by
  constructor
  · exact reflectedPhysical_generator_mem_neumann_graph L hL D hD
  · intro hg
    apply (reflectedGaussianPhysicalL2Curve_generator_iff L hL hD f g).mpr
    exact reflectedNeumann_graph_generator_coefficients L hL D hD hg

end TimeTraps.Probability
