module

public import TimeTraps.Spectral.NetworkOperatorOrderAbsolute
public import TimeTraps.Spectral.NetworkOperatorInverse

@[expose] public section

/-! A nonnegative source in the actual edge L2 Hilbert product pairs
nonpositively with a graph state minus its absolute representative. -/

namespace TimeTraps.Spectral

open Set MeasureTheory InnerProductSpace TimeTraps.Analysis

variable {V E : Type*} [Fintype E] [Nonempty E]

theorem SpectralNetwork.operatorOrderAbs_load_nonpos (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.length e)), 0 ≤ (f e) x)
    (u : GraphSobolevSpace P.geometry) :
    inner ℝ f (graphSobolevSpaceStateL P.geometry (u - P.operatorOrderAbs u)) ≤ 0 := by
  rw [graphL2Product_inner]
  apply Finset.sum_nonpos
  intro e _
  have hs : (graphSobolevSpaceStateL P.geometry (u - P.operatorOrderAbs u)) e =
      (graphSobolevSpaceStateL P.geometry u) e -
        (graphSobolevSpaceStateL P.geometry (P.operatorOrderAbs u)) e := by
    rw [map_sub, PiLp.sub_apply]
  have hrep : (graphSobolevSpaceStateL P.geometry u) e
      =ᵐ[volume.restrict (Ioo 0 (P.length e))] P.operatorRep u e :=
    graphSobolevRepresentative_state_ae P.geometry u.val e
  rw [hs, L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [hf e, Lp.coeFn_sub (graphSobolevSpaceStateL P.geometry u e)
      (graphSobolevSpaceStateL P.geometry (P.operatorOrderAbs u) e),
    hrep, P.operatorOrderAbs_state_ae u e] with x hfx hx hu hv
  simp only [Real.inner_apply, hx, Pi.sub_apply, hu, hv]
  exact mul_nonpos_of_nonneg_of_nonpos hfx (sub_nonpos.mpr (le_abs_self _))

end TimeTraps.Spectral
