module

public import TimeTraps.Spectral.NetworkHeatOrderForm

@[expose] public section

/-! The constant one function is an actual graph H1 state. Its edge
derivatives vanish, while all vertex contact terms remain in its form
pairing. No operator-domain premise is imposed on this supersolution. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*}

theorem networkGraphEnergy_one (G : MetricGraph V E) :
    GraphEnergy G (fun _ => 1) (fun _ _ => 1) :=
  ⟨fun e => IntervalEnergy.const 1 0 (G.length e), fun _ => rfl, fun _ => rfl⟩

noncomputable def SpectralNetwork.operatorOne (P : SpectralNetwork V E) :
    GraphSobolevSpace P.geometry :=
  graphSobolevSpaceOfEnergy P.geometry (networkGraphEnergy_one P.geometry)

theorem SpectralNetwork.operatorOne_representative (P : SpectralNetwork V E) (e : E) :
    EqOn (P.operatorRep P.operatorOne e) (fun _ => 1) (Icc 0 (P.length e)) :=
  P.operatorRep_ofEnergy (networkGraphEnergy_one P.geometry) e

theorem SpectralNetwork.operatorOne_state_ae (P : SpectralNetwork V E) (e : E) :
    (graphSobolevSpaceStateL P.geometry P.operatorOne) e
      =ᵐ[volume.restrict (Ioo 0 (P.length e))] fun _ => 1 :=
  graphSobolevSpaceOfEnergy_state_ae P.geometry (networkGraphEnergy_one P.geometry) e

variable [Nonempty E]

theorem SpectralNetwork.operatorOne_nodes (P : SpectralNetwork V E) (v : V) :
    P.operatorNodes P.operatorOne v = 1 :=
  graphSobolevSpaceOfEnergy_node P.geometry (networkGraphEnergy_one P.geometry) v

variable [Fintype V] [Fintype E]

theorem SpectralNetwork.operatorForm_one (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) :
    P.operatorForm P.operatorOne u = ∑ v, P.strength v * P.operatorNodes u v := by
  have hu : graphSobolevSpaceOfEnergy P.geometry (P.operatorRep_energy u) = u :=
    graphSobolevSpaceOfEnergy_representative_eq P.geometry u
  change P.operatorForm (graphSobolevSpaceOfEnergy P.geometry
    (networkGraphEnergy_one P.geometry)) u = _
  conv_lhs => rw [← hu]
  rw [P.operatorForm_ofEnergy]
  simp only [deriv_const, zero_mul, intervalIntegral.integral_zero, Finset.sum_const_zero,
    mul_zero, zero_add, mul_one]

end TimeTraps.Spectral
