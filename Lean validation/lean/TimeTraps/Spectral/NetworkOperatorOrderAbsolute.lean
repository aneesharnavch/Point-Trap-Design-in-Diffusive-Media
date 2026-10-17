module

public import TimeTraps.Spectral.NetworkOperatorFormPhysical
public import TimeTraps.Analysis.IntervalEnergyAbsolute

@[expose] public section

/-! Absolute value of the physical edge representatives preserves vertex
matching and the full network quadratic form. The resulting element lies
in the actual graph H1 Hilbert space, with no separate nodal coordinates.
Both incidences of loops and all parallel edges are retained. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*}

theorem networkGraphEnergy_abs (G : MetricGraph V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) :
    GraphEnergy G (fun v => |U v|) (fun e x => |u e x|) := by
  refine ⟨fun e => (hu.edge_energy e).abs, ?_, ?_⟩
  · intro e
    exact congrArg abs (hu.tail_value e)
  · intro e
    exact congrArg abs (hu.head_value e)

variable [Nonempty E]

noncomputable def SpectralNetwork.operatorOrderAbs (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) : GraphSobolevSpace P.geometry :=
  graphSobolevSpaceOfEnergy P.geometry (networkGraphEnergy_abs P.geometry (P.operatorRep_energy u))

theorem SpectralNetwork.operatorOrderAbs_state_ae (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) (e : E) :
    (graphSobolevSpaceStateL P.geometry (P.operatorOrderAbs u)) e
      =ᵐ[volume.restrict (Ioo 0 (P.length e))] fun x => |P.operatorRep u e x| :=
  graphSobolevSpaceOfEnergy_state_ae P.geometry
    (networkGraphEnergy_abs P.geometry (P.operatorRep_energy u)) e

theorem SpectralNetwork.operatorOrderAbs_representative (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) (e : E) :
    EqOn (P.operatorRep (P.operatorOrderAbs u) e) (fun x => |P.operatorRep u e x|)
      (Icc 0 (P.length e)) :=
  P.operatorRep_ofEnergy (networkGraphEnergy_abs P.geometry (P.operatorRep_energy u)) e

theorem SpectralNetwork.operatorOrderAbs_nodes (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) (v : V) :
    P.operatorNodes (P.operatorOrderAbs u) v = |P.operatorNodes u v| :=
  graphSobolevSpaceOfEnergy_node P.geometry
    (networkGraphEnergy_abs P.geometry (P.operatorRep_energy u)) v

variable [Fintype V] [Fintype E]

theorem SpectralNetwork.operatorForm_orderAbs (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) :
    P.operatorForm (P.operatorOrderAbs u) (P.operatorOrderAbs u) = P.operatorForm u u := by
  change P.operatorForm
    (graphSobolevSpaceOfEnergy P.geometry (networkGraphEnergy_abs P.geometry (P.operatorRep_energy u)))
    (graphSobolevSpaceOfEnergy P.geometry (networkGraphEnergy_abs P.geometry (P.operatorRep_energy u))) = _
  rw [P.operatorForm_ofEnergy, P.operatorForm_apply]
  simp only [mul_assoc, ← pow_two, sq_abs]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact ((P.operatorRep_energy u).edge_energy e).abs_derivative_energy

end TimeTraps.Spectral
