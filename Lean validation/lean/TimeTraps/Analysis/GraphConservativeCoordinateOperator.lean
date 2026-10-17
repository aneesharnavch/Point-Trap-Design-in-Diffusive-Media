module

public import TimeTraps.Analysis.GraphConservativeCoordinateTestData
public import TimeTraps.Analysis.GraphConservativeVariationData

@[expose] public section

/-! The coordinate equation holds against every original graph H1 test.
Consequently the actual continuous coordinate and the negative of its
divergence-form generator belong to the original unshifted operator graph. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Nonempty E] in
theorem graphConservative_equations_weak (G : MetricGraph V E)
    (κ U W : V → ℝ) (hκ : ∀ v, κ v = 0) (u j h w : E → ℝ → ℝ)
    (heq : ∀ e, EdgeEquation (G.conductance e) (fun x => -h e x)
      0 (G.length e) (u e) (j e))
    (hh : ∀ e, ContinuousOn (h e) (Icc 0 (G.length e)))
    (hj : ∀ e, j e 0 = 0 ∧ j e (G.length e) = 0) (hw : GraphEnergy G W w) :
    graphContactForm G κ U W u w =
      ∑ e, ∫ x in (0 : ℝ)..G.length e, -h e x * w e x := by
  simp only [graphContactForm, hκ, zero_mul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro e _
  simpa only [(hj e).1, (hj e).2, zero_mul, add_zero, sub_zero] using
    (heq e).green_identity_energy (G.length_pos e).le (hh e).neg
      (fun x hx => (G.conductance_pos e x hx).ne') (hw.edge_energy e)

theorem GraphShiftedContactOperatorProblem.graph_of_conservative_equations
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (f g : C(GraphRealization P.geometry, ℝ)) (U : V → ℝ) (u j h : E → ℝ → ℝ)
    (hu : GraphEnergy P.geometry U u)
    (hf : ∀ e (x : Icc (0 : ℝ) (P.geometry.length e)), f (P.geometry.edgePoint e x) = u e x.val)
    (hg : ∀ e (x : Icc (0 : ℝ) (P.geometry.length e)), g (P.geometry.edgePoint e x) = h e x.val)
    (heq : ∀ e, EdgeEquation (P.geometry.conductance e) (fun x => -h e x)
      0 (P.geometry.length e) (u e) (j e))
    (hh : ∀ e, ContinuousOn (h e) (Icc 0 (P.geometry.length e)))
    (hj : ∀ e, j e 0 = 0 ∧ j e (P.geometry.length e) = 0) :
    (graphConservativeContinuousStateL P.geometry f,
      graphConservativeContinuousStateL P.geometry (-g)) ∈ P.operator.graph := by
  apply (P.operator_graph_physical_iff _ _).mpr
  refine ⟨U, u, hu, ?_, ?_⟩
  · have hf' : graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu) = f := by
      ext p
      obtain ⟨e, x, rfl⟩ := P.geometry.edgePoint_surjective p
      rw [graphRealizedSobolev_ofEnergy, hf]
    rw [← graphConservativeContinuousStateL_sobolev, hf']
  · intro W w hw
    rw [graphConservative_equations_weak P.geometry P.strength U W hκ u j h w heq hh hj hw]
    apply Finset.sum_congr rfl
    intro e _
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (P.geometry.length_pos e).le,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [graphConservativeContinuousStateL_coe P.geometry (-g) e,
      ae_restrict_mem measurableSet_Ioo] with z hz hmem
    rw [hz]
    change -h e z * w e z = -g (P.geometry.edgePoint e
      (projIcc 0 (P.geometry.length e) (P.geometry.length_pos e).le z)) * w e z
    rw [hg, projIcc_of_mem (P.geometry.length_pos e).le (Ioo_subset_Icc_self hmem)]

theorem GraphShiftedContactOperatorProblem.coordinate_operator_graph
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) :
    (graphConservativeContinuousStateL P.geometry (P.geometry.coordinateTest φ),
      graphConservativeContinuousStateL P.geometry (-P.geometry.coordinateGenerator φ))
        ∈ P.operator.graph :=
  P.graph_of_conservative_equations hκ _ _ _ _ _ _ (P.geometry.coordinateEnergy φ)
    (P.geometry.coordinateTest_edge φ) (P.geometry.coordinateGenerator_edge φ)
    (P.geometry.coordinateEdge_equation φ) (P.geometry.coordinateEdgeGenerator_continuous φ)
    (fun e => ⟨(P.geometry.coordinateEdgeFlux_generator_endpoints φ e).1,
      (P.geometry.coordinateEdgeFlux_generator_endpoints φ e).2.1⟩)

end TimeTraps.Analysis
