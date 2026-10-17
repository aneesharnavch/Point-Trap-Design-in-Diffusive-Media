module

public import TimeTraps.Spectral.PlacementGeometry

@[expose] public section

/-! Exact positive cosine pieces on the physical gaps of the candidate placement. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph

variable {n : ℕ}

noncomputable def PlacementProblem.cosinePiece (C : PlacementProblem n)
    (e : Fin (n + 1)) (x : ℝ) : ℝ := Real.cos (C.root * x - C.startAngle e)

noncomputable def PlacementProblem.cosineSlope (C : PlacementProblem n)
    (e : Fin (n + 1)) (x : ℝ) : ℝ := -C.root * Real.sin (C.root * x - C.startAngle e)

theorem PlacementProblem.cosinePiece_continuous (C : PlacementProblem n) (e : Fin (n + 1)) :
    Continuous (C.cosinePiece e) := by unfold cosinePiece; fun_prop

theorem PlacementProblem.cosineSlope_continuous (C : PlacementProblem n) (e : Fin (n + 1)) :
    Continuous (C.cosineSlope e) := by unfold cosineSlope; fun_prop

theorem PlacementProblem.cosinePiece_hasDerivAt (C : PlacementProblem n) (e : Fin (n + 1)) (x : ℝ) :
    HasDerivAt (C.cosinePiece e) (C.cosineSlope e x) x := by
  have h := (((hasDerivAt_id x).const_mul C.root).sub_const (C.startAngle e)).cos
  have he : -Real.sin (C.root * x - C.startAngle e) * (C.root * 1) = C.cosineSlope e x := by
    unfold cosineSlope
    ring
  change HasDerivAt (C.cosinePiece e) (-Real.sin (C.root * x - C.startAngle e) * (C.root * 1)) x at h
  rwa [he] at h

theorem PlacementProblem.cosineSlope_hasDerivAt (C : PlacementProblem n) (e : Fin (n + 1)) (x : ℝ) :
    HasDerivAt (C.cosineSlope e) (-(C.root ^ 2) * C.cosinePiece e x) x := by
  have h := ((((hasDerivAt_id x).const_mul C.root).sub_const (C.startAngle e)).sin).const_mul (-C.root)
  have he : -C.root * (Real.cos (C.root * x - C.startAngle e) * (C.root * 1)) =
      -(C.root ^ 2) * C.cosinePiece e x := by unfold cosinePiece; ring
  change HasDerivAt (C.cosineSlope e)
    (-C.root * (Real.cos (C.root * x - C.startAngle e) * (C.root * 1))) x at h
  rwa [he] at h

theorem PlacementProblem.cosinePiece_positive (C : PlacementProblem n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (C.optimalPhysical.shooting.gap e)) : 0 < C.cosinePiece e x :=
  Real.cos_pos_of_mem_Ioo (C.gap_phase_mem e hx)

theorem PlacementProblem.cosinePiece_start (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.cosinePiece e 0 = Real.cos (C.startAngle e) := by
  simp [cosinePiece, Real.cos_neg]

theorem PlacementProblem.cosinePiece_end (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.cosinePiece e (C.optimalPhysical.shooting.gap e) = Real.cos (C.endAngle e) := by
  rw [cosinePiece, C.gap_phase_right]

theorem PlacementProblem.cosineSlope_start (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.cosineSlope e 0 = C.root * Real.sin (C.startAngle e) := by
  simp [cosineSlope, Real.sin_neg]

theorem PlacementProblem.cosineSlope_end (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.cosineSlope e (C.optimalPhysical.shooting.gap e) = -C.root * Real.sin (C.endAngle e) := by
  rw [cosineSlope, C.gap_phase_right]

theorem PlacementProblem.cosinePiece_matching (C : PlacementProblem n) (i : Fin n) :
    C.cosinePiece i.castSucc (C.optimalPhysical.shooting.gap i.castSucc) = C.cosinePiece i.succ 0 := by
  rw [C.cosinePiece_start, C.cosinePiece_end, C.startAngle_succ, C.endAngle_castSucc]

theorem PlacementProblem.cosineSlope_reflecting (C : PlacementProblem n) :
    C.cosineSlope 0 0 = 0 ∧
      C.cosineSlope (Fin.last n) (C.optimalPhysical.shooting.gap (Fin.last n)) = 0 := by
  rw [C.cosineSlope_start, C.cosineSlope_end, C.startAngle_zero, C.endAngle_last, Real.sin_zero,
    mul_zero, mul_zero]
  exact ⟨rfl, rfl⟩

theorem PlacementProblem.cosineSlope_jump (C : PlacementProblem n) (i : Fin n) :
    C.diffusivity * (C.cosineSlope i.succ 0 - C.cosineSlope i.castSucc (C.optimalPhysical.shooting.gap i.castSucc)) =
      C.strength i * C.cosinePiece i.castSucc (C.optimalPhysical.shooting.gap i.castSucc) := by
  rw [C.cosineSlope_start, C.cosineSlope_end, C.cosinePiece_end,
    C.startAngle_succ, C.endAngle_castSucc]
  calc
    _ = 2 * C.diffusivity * C.root * Real.sin (C.angle i) := by ring
    _ = _ := C.angle_reaction i

noncomputable def PlacementProblem.cosineNodes (C : PlacementProblem n) : Fin (n + 2) → ℝ :=
  Fin.snoc (fun e => Real.cos (C.startAngle e)) 1

theorem PlacementProblem.cosineGraphEnergy (C : PlacementProblem n) :
    GraphEnergy C.optimalPhysical.geometry.graph C.cosineNodes C.cosinePiece := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact intervalEnergy_of_continuous_derivative (C.optimalPhysical.shooting.gap_pos e).le
      (C.cosinePiece_continuous e).continuousOn (C.cosineSlope_continuous e).continuousOn
      (fun x _ => C.cosinePiece_hasDerivAt e x)
  · intro e
    change C.cosinePiece e 0 = C.cosineNodes e.castSucc
    rw [cosineNodes, Fin.snoc_castSucc, C.cosinePiece_start]
  · intro e
    change C.cosinePiece e (C.optimalPhysical.shooting.gap e) = C.cosineNodes e.succ
    refine Fin.lastCases ?_ (fun i => ?_) e
    · change C.cosinePiece (Fin.last n) (C.optimalPhysical.shooting.gap (Fin.last n)) =
        C.cosineNodes (Fin.last (n + 1))
      rw [cosineNodes, Fin.snoc_last, C.cosinePiece_end, C.endAngle_last, Real.cos_zero]
    · rw [cosineNodes, Fin.succ_castSucc, Fin.snoc_castSucc, C.cosinePiece_end,
        C.startAngle_succ, C.endAngle_castSucc]

end TimeTraps.Spectral
