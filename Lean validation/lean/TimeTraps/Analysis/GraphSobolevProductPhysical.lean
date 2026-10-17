module

public import TimeTraps.Analysis.GraphSobolevProduct

@[expose] public section

/-! The finite Hilbert product has the actual edge energy representatives.
Its norms and state pairing are sums of the physical edge integrals, and
arbitrary edge energy functions enter and recover this product. No vertex
trace condition is added in this product-level correspondence. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph IntervalSobolevSpace
open scoped InnerProductSpace

variable {V E : Type*}

noncomputable def graphSobolevRepresentative (G : MetricGraph V E)
    (u : GraphSobolevProduct G) (e : E) : ℝ → ℝ :=
  (u e).representative (G.length_pos e)

theorem graphSobolevRepresentative_energy (G : MetricGraph V E)
    (u : GraphSobolevProduct G) (e : E) :
    IntervalEnergy (graphSobolevRepresentative G u e) 0 (G.length e) :=
  ((u e).representative_spec (G.length_pos e)).1

theorem graphSobolevRepresentative_state_ae (G : MetricGraph V E)
    (u : GraphSobolevProduct G) (e : E) :
    (graphSobolevStateL G u) e =ᵐ[volume.restrict (Ioo 0 (G.length e))]
      graphSobolevRepresentative G u e :=
  ((u e).representative_spec (G.length_pos e)).2.1

theorem graphSobolevProduct_norm_sq_integral [Fintype E] (G : MetricGraph V E)
    (u : GraphSobolevProduct G) :
    ‖u‖ ^ 2 = ∑ e, intervalH1SizeSq (graphSobolevRepresentative G u e) 0 (G.length e) := by
  rw [graphSobolevProduct_norm_sq]
  apply Finset.sum_congr rfl
  intro e _
  exact (u e).norm_sq_eq_h1SizeSq (G.length_pos e)

theorem graphSobolevStateL_inner_integral [Fintype E] (G : MetricGraph V E)
    (u v : GraphSobolevProduct G) :
    ⟪graphSobolevStateL G u, graphSobolevStateL G v⟫_ℝ =
      ∑ e, ∫ x in (0 : ℝ)..G.length e,
        graphSobolevRepresentative G u e x * graphSobolevRepresentative G v e x := by
  rw [graphL2Product_inner]
  apply Finset.sum_congr rfl
  intro e _
  exact state_inner (u e) (v e) (G.length_pos e)

theorem graphSobolevStateL_norm_sq_integral [Fintype E] (G : MetricGraph V E)
    (u : GraphSobolevProduct G) :
    ‖graphSobolevStateL G u‖ ^ 2 =
      ∑ e, ∫ x in (0 : ℝ)..G.length e, graphSobolevRepresentative G u e x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, graphSobolevStateL_inner_integral]
  simp only [pow_two]

noncomputable def graphSobolevOfEnergy (G : MetricGraph V E)
    {u : E → ℝ → ℝ} (hu : ∀ e, IntervalEnergy (u e) 0 (G.length e)) :
    GraphSobolevProduct G :=
  WithLp.toLp 2 (fun e => IntervalSobolevSpace.ofEnergy (hu e) (G.length_pos e))

theorem graphSobolevOfEnergy_representative (G : MetricGraph V E)
    {u : E → ℝ → ℝ} (hu : ∀ e, IntervalEnergy (u e) 0 (G.length e)) (e : E) :
    EqOn (graphSobolevRepresentative G (graphSobolevOfEnergy G hu) e) (u e)
      (Icc 0 (G.length e)) := representative_ofEnergy (hu e) (G.length_pos e)

theorem graphSobolevOfEnergy_state_ae (G : MetricGraph V E)
    {u : E → ℝ → ℝ} (hu : ∀ e, IntervalEnergy (u e) 0 (G.length e)) (e : E) :
    (graphSobolevStateL G (graphSobolevOfEnergy G hu)) e
      =ᵐ[volume.restrict (Ioo 0 (G.length e))] u e :=
  (IntervalSobolevSpace.ofEnergy_spec (hu e) (G.length_pos e)).1

theorem graphSobolevOfEnergy_representative_eq (G : MetricGraph V E)
    (u : GraphSobolevProduct G) :
    graphSobolevOfEnergy G (graphSobolevRepresentative_energy G u) = u := by
  apply PiLp.ext
  intro e
  exact IntervalSobolevSpace.ofEnergy_representative (u e) (G.length_pos e)

end TimeTraps.Analysis
