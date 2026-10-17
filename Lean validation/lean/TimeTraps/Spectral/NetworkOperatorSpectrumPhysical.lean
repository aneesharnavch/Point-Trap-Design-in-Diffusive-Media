module

public import TimeTraps.Spectral.NetworkOperatorSpectrum

@[expose] public section

/-! Exact correspondence of operator eigenvectors with the original
full-test network eigen-equation. The physical mass pairing is proved
from the genuine edge L2 product and continuous H1 representatives. -/

namespace TimeTraps.Spectral

open Set MeasureTheory InnerProductSpace TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Fintype V] [Nonempty E] in
theorem SpectralNetwork.operatorState_inner_ofEnergy (P : SpectralNetwork V E)
    {U W : V → ℝ} {u w : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) (hw : GraphEnergy P.geometry W w) :
    inner ℝ (graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu))
      (graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hw)) =
        ∑ e, ∫ x in (0 : ℝ)..P.length e, u e x * w e x := by
  change inner ℝ
    (graphSobolevStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu).val)
    (graphSobolevStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hw).val) = _
  rw [graphSobolevStateL_inner_integral]
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr_Ioo_of_le (P.length_pos e).le
  intro x hx
  dsimp only
  rw [graphSobolevSpaceOfEnergy_representative P.geometry hu e (Ioo_subset_Icc_self hx),
    graphSobolevSpaceOfEnergy_representative P.geometry hw e (Ioo_subset_Icc_self hx)]

omit [Fintype V] [Nonempty E] in
theorem SpectralNetwork.operatorState_norm_ofEnergy (P : SpectralNetwork V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy P.geometry U u) :
    ‖graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu)‖ ^ 2 =
      P.squareMass u := by
  rw [← real_inner_self_eq_norm_sq, P.operatorState_inner_ofEnergy hu hu]
  simp only [SpectralNetwork.squareMass, pow_two]

theorem SpectralNetwork.operator_eigen_iff_hilbert (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) (ev : ℝ) :
    (graphSobolevSpaceStateL P.geometry u, ev • graphSobolevSpaceStateL P.geometry u)
      ∈ P.operator.graph ↔ ∀ v : GraphSobolevSpace P.geometry,
        P.operatorForm u v = ev * inner ℝ (graphSobolevSpaceStateL P.geometry u)
          (graphSobolevSpaceStateL P.geometry v) := by
  rw [P.operator_graph_iff_hilbert]
  constructor
  · rintro ⟨w, hw, he⟩
    have hwu : w = u := graphSobolevSpaceStateL_injective P.geometry hw
    subst w
    simpa only [real_inner_smul_left] using he
  · intro he
    exact ⟨u, rfl, by simpa only [real_inner_smul_left] using he⟩

theorem SpectralNetwork.operator_eigen_iff_physical (P : SpectralNetwork V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy P.geometry U u) (ev : ℝ) :
    (graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu),
      ev • graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu))
        ∈ P.operator.graph ↔ NetworkWeakEigenEquation P ev U u := by
  rw [P.operator_eigen_iff_hilbert]
  constructor
  · intro he
    refine ⟨hu, ?_⟩
    intro W w hw
    have h := he (graphSobolevSpaceOfEnergy P.geometry hw)
    rwa [P.operatorForm_ofEnergy_physical hu hw, P.operatorState_inner_ofEnergy hu hw] at h
  · intro he v
    have hv : graphSobolevSpaceOfEnergy P.geometry (P.operatorRep_energy v) = v :=
      graphSobolevSpaceOfEnergy_representative_eq P.geometry v
    rw [← hv, P.operatorForm_ofEnergy_physical hu (P.operatorRep_energy v),
      P.operatorState_inner_ofEnergy hu (P.operatorRep_energy v)]
    exact he.weak_form (P.operatorNodes v) (P.operatorRep v) (P.operatorRep_energy v)

theorem SpectralNetwork.operator_eigen_iff_representative (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) (ev : ℝ) :
    (graphSobolevSpaceStateL P.geometry u, ev • graphSobolevSpaceStateL P.geometry u)
      ∈ P.operator.graph ↔
        NetworkWeakEigenEquation P ev (P.operatorNodes u) (P.operatorRep u) := by
  have he := P.operator_eigen_iff_physical (P.operatorRep_energy u) ev
  have hu : graphSobolevSpaceOfEnergy P.geometry (P.operatorRep_energy u) = u :=
    graphSobolevSpaceOfEnergy_representative_eq P.geometry u
  rwa [hu] at he

theorem SpectralNetwork.eigenstate_physical_weak (P : SpectralNetwork V E)
    (i : CompactSpectralIndex P.operatorInverse) :
    NetworkWeakEigenEquation P i.1⁻¹
      (P.operatorNodes (P.eigenstate i)) (P.operatorRep (P.eigenstate i)) := by
  apply (P.operator_eigen_iff_representative (P.eigenstate i) i.1⁻¹).mp
  rw [P.eigenstate_state]
  exact P.eigenbasis_operator_graph i

end TimeTraps.Spectral
