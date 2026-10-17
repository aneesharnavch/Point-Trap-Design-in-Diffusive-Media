module

public import TimeTraps.Spectral.NetworkOperatorOrderSolution

@[expose] public section

/-! The actual network inverse and its physical solution preserve the
edgewise almost-everywhere order of arbitrary L2 sources. Representative
comparisons hold on every closed edge and at every node. No heat or
Markov interpretation is asserted. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem SpectralNetwork.operatorInverse_mono_ae (P : SpectralNetwork V E)
    (f g : GraphL2Product P.geometry)
    (hfg : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.length e)), (f e) x ≤ (g e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.length e)),
      (P.operatorInverse f e) x ≤ (P.operatorInverse g e) x := by
  have hp : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.length e)), 0 ≤ ((g - f) e) x := by
    intro e
    simp only [PiLp.sub_apply]
    filter_upwards [hfg e, Lp.coeFn_sub (g e) (f e)] with x hx he
    simpa only [he, Pi.sub_apply] using sub_nonneg.mpr hx
  intro e
  have hi := P.operatorInverse_nonneg_ae (g - f) hp e
  rw [map_sub] at hi
  simp only [PiLp.sub_apply] at hi
  filter_upwards [hi, Lp.coeFn_sub (P.operatorInverse g e) (P.operatorInverse f e)] with x hx he
  apply sub_nonneg.mp
  simpa only [he, Pi.sub_apply] using hx

theorem SpectralNetwork.operatorSolution_representative_mono (P : SpectralNetwork V E)
    (f g : GraphL2Product P.geometry)
    (hfg : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.length e)), (f e) x ≤ (g e) x) :
    ∀ e, ∀ x ∈ Icc 0 (P.length e), P.operatorRep (P.operatorSolution f) e x ≤
      P.operatorRep (P.operatorSolution g) e x := by
  have hp : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.length e)), 0 ≤ ((g - f) e) x := by
    intro e
    simp only [PiLp.sub_apply]
    filter_upwards [hfg e, Lp.coeFn_sub (g e) (f e)] with x hx he
    simpa only [he, Pi.sub_apply] using sub_nonneg.mpr hx
  intro e x hx
  have hi := P.operatorSolution_representative_nonneg (g - f) hp e x hx
  change 0 ≤ evalL (P.length_pos e) x hx
    (P.operatorEdgeL e (P.operatorSolution (g - f))) at hi
  rw [map_sub P.operatorSolution g f, map_sub (P.operatorEdgeL e), map_sub] at hi
  exact sub_nonneg.mp hi

theorem SpectralNetwork.operatorSolution_nodes_mono (P : SpectralNetwork V E)
    (f g : GraphL2Product P.geometry)
    (hfg : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.length e)), (f e) x ≤ (g e) x) :
    ∀ v, P.operatorNodes (P.operatorSolution f) v ≤ P.operatorNodes (P.operatorSolution g) v := by
  have hp : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.length e)), 0 ≤ ((g - f) e) x := by
    intro e
    simp only [PiLp.sub_apply]
    filter_upwards [hfg e, Lp.coeFn_sub (g e) (f e)] with x hx he
    simpa only [he, Pi.sub_apply] using sub_nonneg.mpr hx
  intro v
  have hi := P.operatorSolution_nodes_nonneg (g - f) hp v
  change 0 ≤ graphSobolevNodeValueL P.geometry v (P.operatorSolution (g - f)) at hi
  rw [map_sub P.operatorSolution g f, map_sub] at hi
  exact sub_nonneg.mp hi

theorem NetworkL2WeakEquation.mono_of_source_le {P : SpectralNetwork V E}
    {f g : GraphL2Product P.geometry} {U W : V → ℝ} {u w : E → ℝ → ℝ}
    (hu : NetworkL2WeakEquation P f U u) (hw : NetworkL2WeakEquation P g W w)
    (hfg : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.length e)), (f e) x ≤ (g e) x) :
    (∀ v, U v ≤ W v) ∧ ∀ e, ∀ x ∈ Icc 0 (P.length e), u e x ≤ w e x := by
  have hU := P.operatorNodes_ofEnergy hu.energy
  have hW := P.operatorNodes_ofEnergy hw.energy
  rw [hu.to_operatorSolution] at hU
  rw [hw.to_operatorSolution] at hW
  constructor
  · rw [← hU, ← hW]
    exact P.operatorSolution_nodes_mono f g hfg
  · intro e x hx
    have heu := P.operatorRep_ofEnergy hu.energy e hx
    have hew := P.operatorRep_ofEnergy hw.energy e hx
    rw [hu.to_operatorSolution] at heu
    rw [hw.to_operatorSolution] at hew
    rw [← heu, ← hew]
    exact P.operatorSolution_representative_mono f g hfg e x hx

end TimeTraps.Spectral
