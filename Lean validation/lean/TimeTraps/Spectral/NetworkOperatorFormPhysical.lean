module

public import TimeTraps.Spectral.NetworkOperatorForm

@[expose] public section

/-! The bounded form evaluates to the original physical network pairing
for every graph energy function, including its recovered vertex values. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Fintype V] [Fintype E] in
theorem SpectralNetwork.operatorNodes_ofEnergy (P : SpectralNetwork V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy P.geometry U u) :
    P.operatorNodes (graphSobolevSpaceOfEnergy P.geometry hu) = U := by
  funext v
  exact graphSobolevSpaceOfEnergy_node P.geometry hu v

omit [Fintype V] [Fintype E] [Nonempty E] in
theorem SpectralNetwork.operatorRep_ofEnergy (P : SpectralNetwork V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy P.geometry U u) (e : E) :
    EqOn (P.operatorRep (graphSobolevSpaceOfEnergy P.geometry hu) e) (u e)
      (Icc 0 (P.length e)) := graphSobolevSpaceOfEnergy_representative P.geometry hu e

theorem SpectralNetwork.operatorForm_ofEnergy (P : SpectralNetwork V E)
    {U W : V → ℝ} {u w : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) (hw : GraphEnergy P.geometry W w) :
    P.operatorForm (graphSobolevSpaceOfEnergy P.geometry hu) (graphSobolevSpaceOfEnergy P.geometry hw) =
      P.diffusivity * (∑ e, ∫ x in (0 : ℝ)..P.length e, deriv (u e) x * deriv (w e) x) +
        ∑ v, P.strength v * U v * W v := by
  rw [P.operatorForm_apply, P.operatorNodes_ofEnergy hu, P.operatorNodes_ofEnergy hw]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr_Ioo_of_le (P.length_pos e).le
  intro x hx
  change deriv (P.operatorRep (graphSobolevSpaceOfEnergy P.geometry hu) e) x *
    deriv (P.operatorRep (graphSobolevSpaceOfEnergy P.geometry hw) e) x = deriv (u e) x * deriv (w e) x
  rw [((P.operatorRep_ofEnergy hu e).mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx,
    ((P.operatorRep_ofEnergy hw e).mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx]

theorem SpectralNetwork.operatorForm_ofEnergy_physical (P : SpectralNetwork V E)
    {U W : V → ℝ} {u w : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) (hw : GraphEnergy P.geometry W w) :
    P.operatorForm (graphSobolevSpaceOfEnergy P.geometry hu) (graphSobolevSpaceOfEnergy P.geometry hw) =
      (∑ e, ∫ x in (0 : ℝ)..P.length e, P.diffusivity * deriv (u e) x * deriv (w e) x) +
        ∑ v, P.strength v * U v * W v := by
  rw [P.operatorForm_ofEnergy hu hw]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext x
  ring

end TimeTraps.Spectral
