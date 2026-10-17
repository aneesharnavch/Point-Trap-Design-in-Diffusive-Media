module

public import TimeTraps.Spectral.NetworkOperatorFormCoercive
public import TimeTraps.Spectral.NetworkOperatorFormPhysical
public import TimeTraps.Analysis.GeneralIntervalPointWeak
public import TimeTraps.Analysis.LaxMilgramOperator

@[expose] public section

/-! The actual bounded-linear Lax--Milgram solution map for the original
network and arbitrary edge L2 forcing. Its domain is the independent edge
L2 Hilbert product; its range is the full vertex-continuous H1 space. -/

namespace TimeTraps.Spectral

open Set MeasureTheory InnerProductSpace TimeTraps.Analysis TimeTraps.Graph IntervalSobolevSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def SpectralNetwork.operatorLoad (P : SpectralNetwork V E) :
    GraphL2Product P.geometry →L[ℝ] GraphSobolevSpace P.geometry →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (GraphSobolevSpace P.geometry) :=
    Submodule.seminormedAddCommGroup (graphSobolevSubspace P.geometry)
  letI : NormedSpace ℝ (GraphSobolevSpace P.geometry) :=
    Submodule.normedSpace (graphSobolevSubspace P.geometry)
  exact ((innerSL ℝ).flip.comp (graphSobolevSpaceStateL P.geometry)).flip

omit [Fintype V] [Nonempty E] in
theorem SpectralNetwork.operatorLoad_apply (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) (v : GraphSobolevSpace P.geometry) :
    P.operatorLoad f v = inner ℝ f (graphSobolevSpaceStateL P.geometry v) := rfl

omit [Fintype V] [Nonempty E] in
theorem SpectralNetwork.operatorLoad_representative (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) (v : GraphSobolevSpace P.geometry) :
    P.operatorLoad f v = ∑ e, ∫ x in (0 : ℝ)..P.length e, (f e) x * P.operatorRep v e x := by
  rw [P.operatorLoad_apply, graphL2Product_inner]
  apply Finset.sum_congr rfl
  intro e _
  exact intervalSobolevL2Load_representative (P.length_pos e) (f e) (v.val e)

omit [Fintype V] [Nonempty E] in
theorem SpectralNetwork.operatorLoad_ofEnergy (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) :
    P.operatorLoad f (graphSobolevSpaceOfEnergy P.geometry hu) =
      ∑ e, ∫ x in (0 : ℝ)..P.length e, (f e) x * u e x := by
  rw [P.operatorLoad_apply, graphL2Product_inner]
  apply Finset.sum_congr rfl
  intro e _
  exact intervalSobolevL2Load_ofEnergy (P.length_pos e) (f e) (hu.edge_energy e)

noncomputable def SpectralNetwork.operatorSolution (P : SpectralNetwork V E) :
    GraphL2Product P.geometry →L[ℝ] GraphSobolevSpace P.geometry := by
  letI : InnerProductSpace ℝ (GraphSobolevProduct P.geometry) :=
    PiLp.innerProductSpace (fun e : E => IntervalSobolevSpace 0 (P.length e))
  letI : InnerProductSpace ℝ (GraphSobolevSpace P.geometry) :=
    Submodule.innerProductSpace (graphSobolevSubspace P.geometry)
  exact (coerciveFormSolutionL (V := GraphSobolevSpace P.geometry)
    P.operatorForm (by
      obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
      exact ⟨c, hc, fun u => hb u⟩)).comp P.operatorLoad

-- The specification normalizes the two nested Hilbert-space instances
-- against the already constructed continuous-linear solution map.
set_option maxHeartbeats 800000 in
theorem SpectralNetwork.operatorSolution_spec (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) (v : GraphSobolevSpace P.geometry) :
    P.operatorForm (P.operatorSolution f) v = inner ℝ f (graphSobolevSpaceStateL P.geometry v) := by
  let : InnerProductSpace ℝ (GraphSobolevProduct P.geometry) :=
    PiLp.innerProductSpace (fun e : E => IntervalSobolevSpace 0 (P.length e))
  let : InnerProductSpace ℝ (GraphSobolevSpace P.geometry) :=
    Submodule.innerProductSpace (graphSobolevSubspace P.geometry)
  change P.operatorForm ((coerciveFormSolutionL (V := GraphSobolevSpace P.geometry)
    P.operatorForm (by
      obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
      exact ⟨c, hc, fun u => hb u⟩)) (P.operatorLoad f)) v = _
  change _ = P.operatorLoad f v
  exact coerciveFormSolutionL_spec (V := GraphSobolevSpace P.geometry) P.operatorForm
    (by
      obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
      exact ⟨c, hc, fun u => hb u⟩) (P.operatorLoad f) v

theorem SpectralNetwork.operatorSolution_eq_iff (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) (u : GraphSobolevSpace P.geometry) :
    u = P.operatorSolution f ↔ ∀ v : GraphSobolevSpace P.geometry,
      P.operatorForm u v = inner ℝ f (graphSobolevSpaceStateL P.geometry v) := by
  constructor
  · rintro rfl
    exact P.operatorSolution_spec f
  · intro h
    have he : P.operatorForm (u - P.operatorSolution f) (u - P.operatorSolution f) = 0 := by
      rw [map_sub P.operatorForm u (P.operatorSolution f), sub_apply,
        h, P.operatorSolution_spec, sub_self]
    obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
    have hle := hb (u - P.operatorSolution f)
    rw [he] at hle
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    by_contra hn
    have hp : 0 < ‖u - P.operatorSolution f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    exact (not_le_of_gt (mul_pos (mul_pos hc hp) hp)) hle

end TimeTraps.Spectral
