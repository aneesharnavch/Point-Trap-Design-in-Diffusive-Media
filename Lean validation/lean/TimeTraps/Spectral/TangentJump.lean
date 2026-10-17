module

public import TimeTraps.Spectral.PhaseJump

@[expose] public section

/-! The sharp tangent-jump inequality on the positive principal-phase branch. -/

namespace TimeTraps.Spectral

open Set

theorem positive_phase_difference_mem {a b c : ℝ} (hc : 0 < c)
    (ha : a ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hb : b ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hj : Real.tan b - Real.tan a = c) : b - a ∈ Ioo 0 Real.pi := by
  have htan : Real.tan a < Real.tan b := by linarith
  have h := Real.arctan_strictMono htan
  rw [Real.arctan_tan ha.1 ha.2, Real.arctan_tan hb.1 hb.2] at h
  constructor <;> linarith [ha.1, hb.2]

theorem sharp_tangent_jump {a b c : ℝ} (hc : 0 < c)
    (ha : a ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hb : b ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hj : Real.tan b - Real.tan a = c) :
    2 * Real.tan ((b - a) / 2) ≤ c ∧
      (2 * Real.tan ((b - a) / 2) = c ↔ b = -a) := by
  have hd := positive_phase_difference_mem hc ha hb hj
  have hhalf : (b - a) / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hd.1, hd.2, Real.pi_pos]
  have harctan : Real.arctan (c / 2) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hs := sharp_phase_jump hc ha hb hj
  have hle : (b - a) / 2 ≤ Real.arctan (c / 2) := by linarith [hs.1]
  have htan := Real.strictMonoOn_tan.monotoneOn hhalf harctan hle
  rw [Real.tan_arctan] at htan
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have he' : Real.tan ((b - a) / 2) = c / 2 := by linarith
    have hi := congrArg Real.arctan he'
    rw [Real.arctan_tan hhalf.1 hhalf.2] at hi
    exact hs.2.mp (by linarith)
  · intro he
    have hi : (b - a) / 2 = Real.arctan (c / 2) := by linarith [hs.2.mpr he]
    rw [hi, Real.tan_arctan]
    ring

end TimeTraps.Spectral
