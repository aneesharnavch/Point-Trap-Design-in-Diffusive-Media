module

public import TimeTraps.Analysis.RegularSturmCoercivity
public import TimeTraps.Analysis.LaxMilgramOperator

@[expose] public section

/-! The original full separated-endpoint H1 shifted solution and compact
inverse in the physical speed-weighted Hilbert representation. The load
is the actual weighted-state dual pairing; no eigenstate or regularity
certificate is assumed as input. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable section

def RegularSturmProblem.load (P : RegularSturmProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSeparatedSpace P.boundary →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (IntervalSeparatedSpace P.boundary) :=
    Submodule.seminormedAddCommGroup P.boundary.subspace
  letI : NormedSpace ℝ (IntervalSeparatedSpace P.boundary) :=
    Submodule.normedSpace P.boundary.subspace
  exact (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ (IntervalSobolevL2 l r)) P.stateL

theorem RegularSturmProblem.load_apply (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalSeparatedSpace P.boundary) :
    P.load f v = inner ℝ f (P.stateL v) := rfl

def RegularSturmProblem.shiftedSolution (P : RegularSturmProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSeparatedSpace P.boundary :=
  (coerciveFormSolutionL (V := IntervalSeparatedSpace P.boundary) P.shiftedForm P.shiftedForm_coercive).comp P.load

def RegularSturmProblem.shiftedInverse (P : RegularSturmProblem ι l r) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSobolevL2 l r :=
  P.stateL.comp P.shiftedSolution

-- Normalizing the nested subspace instances in the generic solution theorem
-- requires a larger elaboration budget; the Hilbert space and form are unchanged.
set_option maxHeartbeats 800000 in
theorem RegularSturmProblem.shiftedSolution_spec (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) (v : IntervalSeparatedSpace P.boundary) :
    P.shiftedForm (P.shiftedSolution f) v = inner ℝ f (P.stateL v) := by
  simpa only [RegularSturmProblem.shiftedSolution, ContinuousLinearMap.comp_apply] using
    (coerciveFormSolutionL_spec (V := IntervalSeparatedSpace P.boundary)
      P.shiftedForm P.shiftedForm_coercive (P.load f) v).trans (P.load_apply f v)

theorem RegularSturmProblem.shiftedInverse_apply (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) : P.shiftedInverse f = P.stateL (P.shiftedSolution f) := rfl

theorem RegularSturmProblem.shiftedInverse_compact (P : RegularSturmProblem ι l r) :
    IsCompactOperator P.shiftedInverse := P.stateL_compact.comp_clm P.shiftedSolution

theorem RegularSturmProblem.shiftedSolution_eq_iff (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) (u : IntervalSeparatedSpace P.boundary) :
    u = P.shiftedSolution f ↔ ∀ v : IntervalSeparatedSpace P.boundary,
      P.shiftedForm u v = inner ℝ f (P.stateL v) := by
  constructor
  · rintro rfl
    exact P.shiftedSolution_spec f
  · intro h
    have he : P.shiftedForm (u - P.shiftedSolution f) (u - P.shiftedSolution f) = 0 := by
      rw [map_sub P.shiftedForm u (P.shiftedSolution f), sub_apply, h, P.shiftedSolution_spec, sub_self]
    obtain ⟨c, hc, hb⟩ := P.shiftedForm_coercive
    have hle := hb (u - P.shiftedSolution f)
    rw [he] at hle
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    by_contra hn
    have hp : 0 < ‖u - P.shiftedSolution f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    exact (not_le_of_gt (mul_pos (mul_pos hc hp) hp)) hle

end

end TimeTraps.Analysis
