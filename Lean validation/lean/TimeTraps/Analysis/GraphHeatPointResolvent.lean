module

public import TimeTraps.Analysis.GraphHeatPointResolventSource
public import TimeTraps.Analysis.GraphHeatPointResolventPairing

@[expose] public section

/-! The literal discounted point potential of the actual graph heat is
the unique full-dual point-source weak resolvent. All graph points,
including every vertex, retain their original H1 evaluation. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential_one_eq
    (P : GraphShiftedContactOperatorProblem V E) (a x : GraphRealization P.geometry) :
    P.pointLocalTimeDiscountedPotential a 1 x =
      graphRealizedSobolev P.geometry (P.pointResolventSolution a) x := by
  have hparam : Continuous (fun x : GraphRealization P.geometry => (x, a)) :=
    continuous_id.prodMk continuous_const
  have hR := P.pointLocalTimeDiscountedPotential_continuous (q := 1) (by norm_num)
  have hc := hR.comp hparam
  let r : C(GraphRealization P.geometry, ℝ) := ⟨P.pointLocalTimeDiscountedPotential a 1, hc⟩
  let u := graphRealizedSobolev P.geometry (P.pointResolventSolution a)
  let d := r - u
  have hp (f : C(GraphRealization P.geometry, ℝ)) :
      (∫ y, f y * r y ∂P.geometry.lengthMeasure) =
        ∫ y, f y * u y ∂P.geometry.lengthMeasure :=
    (P.pointLocalTimeDiscountedPotential_one_pairing a f).trans
      (P.pointResolventSolution_length_pairing a f).symm
  have hd : inner ℝ (graphConservativeContinuousStateL P.geometry d)
      (graphConservativeContinuousStateL P.geometry d) = 0 := by
    rw [graphConservativeContinuousStateL_pairing]
    have hir : Integrable (fun y => d y * r y) P.geometry.lengthMeasure :=
      (d.continuous.mul r.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hiu : Integrable (fun y => d y * u y) P.geometry.lengthMeasure :=
      (d.continuous.mul u.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
      _ = (∫ y, d y * r y ∂P.geometry.lengthMeasure) -
          ∫ y, d y * u y ∂P.geometry.lengthMeasure := by
        change (∫ y, d y * (r y - u y) ∂P.geometry.lengthMeasure) = _
        simp_rw [mul_sub]
        exact integral_sub hir hiu
      _ = 0 := sub_eq_zero.mpr (hp d)
  have hz := inner_self_eq_zero.mp hd
  have he : r = u := by
    apply graphConservativeContinuousStateL_injective P.geometry
    apply sub_eq_zero.mp
    simpa only [d, map_sub] using hz
  exact congrArg (fun f : C(GraphRealization P.geometry, ℝ) => f x) he

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential_one_weak
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) :
    ∃ u : GraphSobolevSpace P.geometry,
      (∀ x, P.pointLocalTimeDiscountedPotential a 1 x = graphRealizedSobolev P.geometry u x) ∧
      (∀ v : GraphSobolevSpace P.geometry,
        graphShiftedContactForm P.geometry P.strength
          (P.operatorNodes u) (P.operatorNodes v) (P.operatorRep u) (P.operatorRep v) =
            graphRealizedSobolev P.geometry v a) := by
  refine ⟨P.pointResolventSolution a, P.pointLocalTimeDiscountedPotential_one_eq a, ?_⟩
  intro v
  rw [← P.operatorForm_apply, P.pointResolventSolution_spec]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential_one_vertex
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (v : V) :
    P.pointLocalTimeDiscountedPotential a 1 (P.geometry.vertexPoint v) =
      P.operatorNodes (P.pointResolventSolution a) v := by
  rw [P.pointLocalTimeDiscountedPotential_one_eq, graphRealizedSobolev_vertex]
  rfl

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential_one_edge
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    P.pointLocalTimeDiscountedPotential a 1 (P.geometry.edgePoint e x) =
      P.operatorRep (P.pointResolventSolution a) e x.val := by
  rw [P.pointLocalTimeDiscountedPotential_one_eq, graphRealizedSobolev_edge]
  rfl

end TimeTraps.Analysis
