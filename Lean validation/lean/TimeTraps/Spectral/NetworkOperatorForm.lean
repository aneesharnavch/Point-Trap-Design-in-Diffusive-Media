module

public import TimeTraps.Spectral.NetworkProblem
public import TimeTraps.Analysis.GraphSobolevSpacePhysical
public import TimeTraps.Analysis.IntervalPointFormHilbert

@[expose] public section

/-! The original network form as an actual bounded bilinear map on its
vertex-continuous edge H1 Hilbert space. Vertex values are the recovered
edge traces; the original diffusivity, lengths, and vertex strengths are
unchanged. -/

namespace TimeTraps.Spectral

open Set MeasureTheory InnerProductSpace TimeTraps.Analysis TimeTraps.Graph IntervalSobolevSpace

variable {V E : Type*}

noncomputable def SpectralNetwork.operatorRep (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) : E → ℝ → ℝ :=
  graphSobolevRepresentative P.geometry u.val

noncomputable def SpectralNetwork.operatorNodes [Nonempty E] (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) : V → ℝ := graphSobolevNodeValue P.geometry u

theorem SpectralNetwork.operatorRep_energy [Nonempty E] (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) : GraphEnergy P.geometry (P.operatorNodes u) (P.operatorRep u) :=
  graphSobolevSpace_energy P.geometry u

theorem SpectralNetwork.operator_squareMass [Fintype E] (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) :
    P.squareMass (P.operatorRep u) = ‖graphSobolevSpaceStateL P.geometry u‖ ^ 2 :=
  (graphSobolevStateL_norm_sq_integral P.geometry u.val).symm

theorem SpectralNetwork.operator_norm_sq [Fintype E] (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) :
    ‖u‖ ^ 2 = P.squareMass (P.operatorRep u) +
      ∑ e, ∫ x in (0 : ℝ)..P.length e, deriv (P.operatorRep u e) x ^ 2 := by
  change ‖u.val‖ ^ 2 = _
  rw [graphSobolevProduct_norm_sq_integral]
  simp only [intervalH1SizeSq, Finset.sum_add_distrib]
  rfl

noncomputable def SpectralNetwork.operatorEdgeL (P : SpectralNetwork V E) (e : E) :
    GraphSobolevSpace P.geometry →L[ℝ] IntervalSobolevSpace 0 (P.length e) :=
  (graphSobolevComponentL P.geometry e).comp (graphSobolevSubspace P.geometry).subtypeL

variable [Fintype V] [Fintype E] [Nonempty E]

noncomputable def SpectralNetwork.operatorForm (P : SpectralNetwork V E) :
    GraphSobolevSpace P.geometry →L[ℝ] GraphSobolevSpace P.geometry →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (GraphSobolevSpace P.geometry) :=
    Submodule.seminormedAddCommGroup (graphSobolevSubspace P.geometry)
  letI : NormedSpace ℝ (GraphSobolevSpace P.geometry) :=
    Submodule.normedSpace (graphSobolevSubspace P.geometry)
  exact P.diffusivity • (∑ e, (intervalSobolevGradientForm 0 (P.length e)).bilinearComp
    (P.operatorEdgeL e) (P.operatorEdgeL e)) +
    ∑ v, P.strength v • (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (graphSobolevNodeValueL P.geometry v) (graphSobolevNodeValueL P.geometry v)

theorem SpectralNetwork.operatorForm_apply (P : SpectralNetwork V E)
    (u w : GraphSobolevSpace P.geometry) :
    P.operatorForm u w =
      P.diffusivity * (∑ e, ∫ x in (0 : ℝ)..P.length e,
        deriv (P.operatorRep u e) x * deriv (P.operatorRep w e) x) +
      ∑ v, P.strength v * P.operatorNodes u v * P.operatorNodes w v := by
  simp only [operatorForm, intervalSobolevGradientForm, add_apply, smul_apply, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul]
  change P.diffusivity * (∑ e, inner ℝ (u.val e).gradient (w.val e).gradient) +
    ∑ v, P.strength v * (P.operatorNodes u v * P.operatorNodes w v) = _
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro e _
    exact gradient_inner (u.val e) (w.val e) (P.length_pos e)
  · apply Finset.sum_congr rfl
    intro v _
    ring

theorem SpectralNetwork.operatorForm_self (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) :
    P.operatorForm u u = P.quadraticForm (P.operatorNodes u) (P.operatorRep u) := by
  rw [P.operatorForm_apply]
  simp only [quadraticForm, pow_two, mul_assoc]

theorem SpectralNetwork.operatorForm_nonneg (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) : 0 ≤ P.operatorForm u u := by
  rw [P.operatorForm_self]
  exact P.quadraticForm_nonneg _ _

theorem SpectralNetwork.operatorForm_symmetric (P : SpectralNetwork V E)
    (u w : GraphSobolevSpace P.geometry) : P.operatorForm u w = P.operatorForm w u := by
  rw [P.operatorForm_apply, P.operatorForm_apply]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro e _
    congr 1
    funext x
    ring
  · apply Finset.sum_congr rfl
    intro v _
    ring

end TimeTraps.Spectral
