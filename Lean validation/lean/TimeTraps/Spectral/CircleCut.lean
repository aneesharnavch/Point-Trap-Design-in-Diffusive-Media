module

public import TimeTraps.Spectral.CircleGeometry
public import TimeTraps.Interval.GeneralEnergyAssembly

@[expose] public section

/-! Cut the anchored circle into its actual physical interval. The first trap
is duplicated only as an endpoint trace; no extra reaction is introduced. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph

variable {n : ℕ}

noncomputable def CircleProblem.cut (C : CircleProblem (n + 1)) : OrderedMedium n where
  source := {
    left := 0
    right := C.length
    increasing := C.length_pos
    density := fun _ => 1
    continuous := continuousOn_const
    positive := fun _ _ => zero_lt_one }
  conductance := fun _ => C.diffusivity
  conductance_continuous := continuousOn_const
  conductance_pos := fun _ _ => C.diffusivity_pos
  node := C.boundary
  node_strictMono := C.boundary_strictMono
  node_first := C.boundary_zero
  node_last := C.boundary_last

theorem CircleProblem.cut_gapLength (C : CircleProblem (n + 1)) (e : Fin (n + 1)) :
    C.cut.gapLength e = C.gap e := by
  change C.boundary e.succ - C.boundary e.castSucc = C.gap e
  rw [C.boundary_succ]
  change C.site e + C.gap e - C.site e = C.gap e
  ring

def circleCutNodes (U : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ := Fin.snoc U (U 0)

theorem circleCutNodes_castSucc (U : Fin (n + 1) → ℝ) (e : Fin (n + 1)) :
    circleCutNodes U e.castSucc = U e := by simp [circleCutNodes]

theorem circleCutNodes_first (U : Fin (n + 1) → ℝ) : circleCutNodes U 0 = U 0 := by
  change circleCutNodes U (0 : Fin (n + 1)).castSucc = U 0
  exact circleCutNodes_castSucc U 0

theorem circleCutNodes_last (U : Fin (n + 1) → ℝ) :
    circleCutNodes U (Fin.last (n + 1)) = U 0 := by simp [circleCutNodes]

theorem circleCutNodes_succ (U : Fin (n + 1) → ℝ) (e : Fin (n + 1)) :
    circleCutNodes U e.succ = U (finRotate (n + 1) e) := by
  refine Fin.lastCases ?_ (fun i => ?_) e
  · rw [finRotate_last]
    exact circleCutNodes_last U
  · have hr : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
    rw [hr, Fin.succ_castSucc, circleCutNodes_castSucc]

theorem CircleProblem.to_cut_energy (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy C.network.geometry U u) : GraphEnergy C.cut.graph (circleCutNodes U) u := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    change IntervalEnergy (u e) 0 (C.cut.gapLength e)
    rw [C.cut_gapLength]
    exact hu.edge_energy e
  · intro e
    change u e 0 = circleCutNodes U e.castSucc
    rw [circleCutNodes_castSucc]
    exact hu.tail_value e
  · intro e
    change u e (C.cut.gapLength e) = circleCutNodes U e.succ
    rw [C.cut_gapLength, circleCutNodes_succ]
    exact hu.head_value e

theorem CircleProblem.from_cut_energy (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy C.cut.graph (circleCutNodes U) u) : GraphEnergy C.network.geometry U u := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have h := hu.edge_energy e
    change IntervalEnergy (u e) 0 (C.cut.gapLength e) at h
    rwa [C.cut_gapLength] at h
  · intro e
    have h := hu.tail_value e
    change u e 0 = circleCutNodes U e.castSucc at h
    rwa [circleCutNodes_castSucc] at h
  · intro e
    have h := hu.head_value e
    change u e (C.cut.gapLength e) = circleCutNodes U e.succ at h
    rwa [C.cut_gapLength, circleCutNodes_succ] at h

theorem CircleProblem.cut_energy_iff (C : CircleProblem (n + 1))
    (U : Fin (n + 1) → ℝ) (u : Fin (n + 1) → ℝ → ℝ) :
    GraphEnergy C.network.geometry U u ↔ GraphEnergy C.cut.graph (circleCutNodes U) u :=
  ⟨C.to_cut_energy, C.from_cut_energy⟩

noncomputable def CircleProblem.assembled (C : CircleProblem (n + 1))
    (U : Fin (n + 1) → ℝ) (u : Fin (n + 1) → ℝ → ℝ) : ℝ → ℝ :=
  C.cut.assembledState (circleCutNodes U) u

theorem CircleProblem.assembled_energy (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy C.network.geometry U u) : IntervalEnergy (C.assembled U u) 0 C.length :=
  C.cut.assembledState_energy_general (C.to_cut_energy hu)

theorem CircleProblem.assembled_site (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy C.network.geometry U u) (i : Fin (n + 1)) :
    C.assembled U u (C.site i) = U i := by
  have h := C.cut.assembledState_node (C.to_cut_energy hu) i.castSucc
  rw [circleCutNodes_castSucc] at h
  exact h

theorem CircleProblem.assembled_periodic (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy C.network.geometry U u) : C.assembled U u 0 = C.assembled U u C.length := by
  have hl := C.cut.assembledState_node (C.to_cut_energy hu) 0
  have hr := C.cut.assembledState_node (C.to_cut_energy hu) (Fin.last (n + 1))
  rw [circleCutNodes_first, C.cut.node_first] at hl
  rw [circleCutNodes_last, C.cut.node_last] at hr
  exact hl.trans hr.symm

theorem CircleProblem.assembled_gap (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy C.network.geometry U u) (i : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc 0 (C.gap i)) : C.assembled U u (C.site i + x) = u i x := by
  apply C.cut.assembledState_gap (C.to_cut_energy hu) i
  rwa [C.cut_gapLength]

theorem CircleProblem.assembled_gap_deriv (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy C.network.geometry U u) (i : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (C.gap i)) : deriv (C.assembled U u) (C.site i + x) = deriv (u i) x := by
  apply C.cut.assembledState_gap_deriv (C.to_cut_energy hu) i
  rwa [C.cut_gapLength]

end TimeTraps.Spectral
