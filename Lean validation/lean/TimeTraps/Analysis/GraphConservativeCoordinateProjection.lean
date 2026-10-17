module

public import TimeTraps.Analysis.GraphConservativeCoordinatePowers

@[expose] public section

/-! Canonical finite scalar projections of the actual separating graph
coordinates. Flattening the three coordinate blocks preserves their
existing product/sup norm exactly, including empty index blocks. -/

namespace TimeTraps.Graph

open TimeTraps.Analysis

abbrev GraphCoordinateIndex (V E : Type*) := V ⊕ (E ⊕ E)

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def graphCoordinateProjection :
    GraphCoordinateIndex V E → GraphRealizationCoordinates V E →L[ℝ] ℝ
  | Sum.inl v => (ContinuousLinearMap.proj v).comp
      (ContinuousLinearMap.fst ℝ (V → ℝ) ((E → ℝ) × (E → ℝ)))
  | Sum.inr (Sum.inl e) => (ContinuousLinearMap.proj e).comp
      ((ContinuousLinearMap.fst ℝ (E → ℝ) (E → ℝ)).comp
        (ContinuousLinearMap.snd ℝ (V → ℝ) ((E → ℝ) × (E → ℝ))))
  | Sum.inr (Sum.inr e) => (ContinuousLinearMap.proj e).comp
      ((ContinuousLinearMap.snd ℝ (E → ℝ) (E → ℝ)).comp
        (ContinuousLinearMap.snd ℝ (V → ℝ) ((E → ℝ) × (E → ℝ))))

omit [Fintype V] [Fintype E] in
theorem graphCoordinateProjection_vertex (v : V) (z : GraphRealizationCoordinates V E) :
    graphCoordinateProjection (Sum.inl v) z = z.1 v := rfl

omit [Fintype V] [Fintype E] in
theorem graphCoordinateProjection_edge_first (e : E) (z : GraphRealizationCoordinates V E) :
    graphCoordinateProjection (Sum.inr (Sum.inl e)) z = z.2.1 e := rfl

omit [Fintype V] [Fintype E] in
theorem graphCoordinateProjection_edge_second (e : E) (z : GraphRealizationCoordinates V E) :
    graphCoordinateProjection (Sum.inr (Sum.inr e)) z = z.2.2 e := rfl

theorem graphCoordinateProjection_norm (z : GraphRealizationCoordinates V E) :
    ‖fun i : GraphCoordinateIndex V E => graphCoordinateProjection i z‖ = ‖z‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    rintro (v | (e | e))
    · exact (norm_le_pi_norm z.1 v).trans (norm_fst_le z)
    · exact ((norm_le_pi_norm z.2.1 e).trans (norm_fst_le z.2)).trans (norm_snd_le z)
    · exact ((norm_le_pi_norm z.2.2 e).trans (norm_snd_le z.2)).trans (norm_snd_le z)
  · rw [Prod.norm_def, Prod.norm_def]
    refine max_le ?_ (max_le ?_ ?_)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro v
      exact norm_le_pi_norm (fun i : GraphCoordinateIndex V E => graphCoordinateProjection i z) (Sum.inl v)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro e
      exact norm_le_pi_norm (fun i : GraphCoordinateIndex V E => graphCoordinateProjection i z) (Sum.inr (Sum.inl e))
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro e
      exact norm_le_pi_norm (fun i : GraphCoordinateIndex V E => graphCoordinateProjection i z) (Sum.inr (Sum.inr e))

end TimeTraps.Graph
