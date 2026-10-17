module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
The sharp phase-jump lemma (`lem:phase` in the primary preprint).
The argument maximizes an arctangent difference on the whole real line.
No spectral existence or ground-state assertion is assumed or proved here.
-/

namespace TimeTraps.Spectral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def phaseJump (c t : ℝ) : ℝ :=
  Real.arctan (t + c) - Real.arctan t

theorem phaseJump_hasDerivAt (c t : ℝ) :
    HasDerivAt (phaseJump c)
      (1 / (1 + (t + c) ^ 2) - 1 / (1 + t ^ 2)) t := by
  have h := (((hasDerivAt_id t).add_const c).arctan).sub (Real.hasDerivAt_arctan t)
  convert! h using 1
  simp [id_eq]

theorem phaseJump_continuous (c : ℝ) : Continuous (phaseJump c) :=
  continuous_iff_continuousAt.mpr fun t => (phaseJump_hasDerivAt c t).continuousAt

theorem phaseJump_strictMonoOn {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (phaseJump c) (Set.Iic (-c / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic _) (phaseJump_continuous c).continuousOn
  intro t ht
  rw [interior_Iic, Set.mem_Iio] at ht
  rw [(phaseJump_hasDerivAt c t).deriv]
  apply sub_pos.mpr
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith

theorem phaseJump_strictAntiOn {c : ℝ} (hc : 0 < c) :
    StrictAntiOn (phaseJump c) (Set.Ici (-c / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (phaseJump_continuous c).continuousOn
  intro t ht
  rw [interior_Ici, Set.mem_Ioi] at ht
  rw [(phaseJump_hasDerivAt c t).deriv]
  apply sub_neg.mpr
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith

theorem phaseJump_at_center (c : ℝ) :
    phaseJump c (-c / 2) = 2 * Real.arctan (c / 2) := by
  unfold phaseJump
  rw [show -c / 2 + c = c / 2 by ring, show -c / 2 = -(c / 2) by ring,
    Real.arctan_neg]
  ring

/-- Strict loss away from the symmetric incident logarithmic derivatives. -/
theorem phaseJump_lt_of_ne {c t : ℝ} (hc : 0 < c) (ht : t ≠ -c / 2) :
    phaseJump c t < 2 * Real.arctan (c / 2) := by
  rw [← phaseJump_at_center]
  rcases lt_or_gt_of_ne ht with ht | ht
  · exact phaseJump_strictMonoOn hc ht.le (by simp only [Set.mem_Iic, le_refl]) ht
  · exact phaseJump_strictAntiOn hc (by simp only [Set.mem_Ici, le_refl]) ht.le ht

theorem phaseJump_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    phaseJump c t ≤ 2 * Real.arctan (c / 2) := by
  by_cases ht : t = -c / 2
  · rw [ht, phaseJump_at_center]
  · exact (phaseJump_lt_of_ne hc ht).le

theorem phaseJump_eq_iff {c t : ℝ} (hc : 0 < c) :
    phaseJump c t = 2 * Real.arctan (c / 2) ↔ t = -c / 2 := by
  constructor
  · intro heq
    by_contra ht
    exact (ne_of_lt (phaseJump_lt_of_ne hc ht)) heq
  · intro ht
    rw [ht, phaseJump_at_center]

/-- The manuscript's statement in principal phases, including iff equality. -/
theorem sharp_phase_jump {c θminus θplus : ℝ} (hc : 0 < c)
    (hminus : θminus ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hplus : θplus ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hjump : Real.tan θplus - Real.tan θminus = c) :
    θplus - θminus ≤ 2 * Real.arctan (c / 2) ∧
      (θplus - θminus = 2 * Real.arctan (c / 2) ↔ θplus = -θminus) := by
  have ht : Real.tan θminus + c = Real.tan θplus := by linarith
  have hvalue : phaseJump c (Real.tan θminus) = θplus - θminus := by
    rw [phaseJump, ht, Real.arctan_tan hplus.1 hplus.2,
      Real.arctan_tan hminus.1 hminus.2]
  refine ⟨hvalue ▸ phaseJump_le hc _, ?_⟩
  rw [← hvalue, phaseJump_eq_iff hc]
  constructor
  · intro hcenter
    have htan : Real.tan θplus = -Real.tan θminus := by linarith
    calc
      θplus = Real.arctan (Real.tan θplus) := (Real.arctan_tan hplus.1 hplus.2).symm
      _ = -θminus := by rw [htan, Real.arctan_neg, Real.arctan_tan hminus.1 hminus.2]
  · intro heq
    rw [heq, Real.tan_neg] at hjump
    linarith

end TimeTraps.Spectral
