module

public import TimeTraps.Spectral.SineFlow
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
Exact Robin shooting with independently prescribed positive gaps and interior
reaction rates and nonnegative endpoint rates. The initial state is (1,leftRate).
The right residual is slope + rightRate * value. No terminal condition or
positive spectral state is assumed.
-/

namespace TimeTraps.Spectral

open Set

structure RobinShootingData (n : ℕ) where
  gap : Fin (n + 1) → ℝ
  gap_pos : ∀ e, 0 < gap e
  reaction : Fin n → ℝ
  reaction_pos : ∀ i, 0 < reaction i
  leftRate : ℝ
  leftRate_nonneg : 0 ≤ leftRate
  rightRate : ℝ
  rightRate_nonneg : 0 ≤ rightRate

variable {n : ℕ}

noncomputable def RobinShootingData.initial (S : RobinShootingData n) (k : ℝ) : Fin (n + 1) → ℝ × ℝ :=
  Fin.induction (1, S.leftRate) (fun i p => reactionJump (S.reaction i) (sineFlow k (S.gap i.castSucc) p))

noncomputable def RobinShootingData.value (S : RobinShootingData n) (k : ℝ) (e : Fin (n + 1)) (x : ℝ) : ℝ :=
  sineValue k (S.initial k e).1 (S.initial k e).2 x

noncomputable def RobinShootingData.slope (S : RobinShootingData n) (k : ℝ) (e : Fin (n + 1)) (x : ℝ) : ℝ :=
  sineSlope k (S.initial k e).1 (S.initial k e).2 x

noncomputable def RobinShootingData.residual (S : RobinShootingData n) (k : ℝ) : ℝ :=
  S.slope k (Fin.last n) (S.gap (Fin.last n)) +
    S.rightRate * S.value k (Fin.last n) (S.gap (Fin.last n))

theorem RobinShootingData.initial_zero (S : RobinShootingData n) (k : ℝ) : S.initial k 0 = (1, S.leftRate) := rfl

theorem RobinShootingData.initial_succ (S : RobinShootingData n) (k : ℝ) (i : Fin n) :
    S.initial k i.succ = reactionJump (S.reaction i) (sineFlow k (S.gap i.castSucc) (S.initial k i.castSucc)) := rfl

theorem RobinShootingData.value_start (S : RobinShootingData n) (k : ℝ) (e : Fin (n + 1)) :
    S.value k e 0 = (S.initial k e).1 := by simp [value, sineValue]

theorem RobinShootingData.slope_start (S : RobinShootingData n) (k : ℝ) (e : Fin (n + 1)) :
    S.slope k e 0 = (S.initial k e).2 := by simp [slope, sineSlope]

theorem RobinShootingData.left_value (S : RobinShootingData n) (k : ℝ) : S.value k 0 0 = 1 := by
  rw [S.value_start, S.initial_zero]

theorem RobinShootingData.left_slope (S : RobinShootingData n) (k : ℝ) : S.slope k 0 0 = S.leftRate := by
  rw [S.slope_start, S.initial_zero]

theorem RobinShootingData.value_matching (S : RobinShootingData n) (k : ℝ) (i : Fin n) :
    S.value k i.succ 0 = S.value k i.castSucc (S.gap i.castSucc) := by
  rw [S.value_start, S.initial_succ]
  rfl

theorem RobinShootingData.slope_jump (S : RobinShootingData n) (k : ℝ) (i : Fin n) :
    S.slope k i.succ 0 = S.slope k i.castSucc (S.gap i.castSucc) +
      S.reaction i * S.value k i.castSucc (S.gap i.castSucc) := by
  rw [S.slope_start, S.initial_succ]
  rfl

theorem RobinShootingData.value_hasDerivAt (S : RobinShootingData n) (k : ℝ) (e : Fin (n + 1)) (x : ℝ) :
    HasDerivAt (S.value k e) (S.slope k e x) x := sineValue_hasDerivAt _ _ _ _

theorem RobinShootingData.slope_hasDerivAt (S : RobinShootingData n) (k : ℝ) (e : Fin (n + 1)) (x : ℝ) :
    HasDerivAt (S.slope k e) (-(k ^ 2) * S.value k e x) x := sineSlope_hasDerivAt _ _ _ _

theorem RobinShootingData.initial_continuous (S : RobinShootingData n) (e : Fin (n + 1)) :
    Continuous (fun k => S.initial k e) := by
  induction e using Fin.induction with
  | zero => exact continuous_const
  | succ i ih =>
    change Continuous (fun k => reactionJump (S.reaction i) (sineFlow k (S.gap i.castSucc) (S.initial k i.castSucc)))
    have hv : Continuous (fun k => sineValue k (S.initial k i.castSucc).1 (S.initial k i.castSucc).2 (S.gap i.castSucc)) :=
      sineValue_continuous.comp (continuous_id.prodMk
      (ih.fst.prodMk (ih.snd.prodMk continuous_const)))
    have hd : Continuous (fun k => sineSlope k (S.initial k i.castSucc).1 (S.initial k i.castSucc).2 (S.gap i.castSucc)) :=
      sineSlope_continuous.comp (continuous_id.prodMk
      (ih.fst.prodMk (ih.snd.prodMk continuous_const)))
    exact hv.prodMk (hd.add (continuous_const.mul hv))

theorem RobinShootingData.value_continuous (S : RobinShootingData n) (e : Fin (n + 1)) :
    Continuous (fun p : ℝ × ℝ => S.value p.1 e p.2) := by
  have hi : Continuous (fun p : ℝ × ℝ => S.initial p.1 e) := (S.initial_continuous e).comp continuous_fst
  exact sineValue_continuous.comp (continuous_fst.prodMk (hi.fst.prodMk (hi.snd.prodMk continuous_snd)))

theorem RobinShootingData.slope_continuous (S : RobinShootingData n) (e : Fin (n + 1)) :
    Continuous (fun p : ℝ × ℝ => S.slope p.1 e p.2) := by
  have hi : Continuous (fun p : ℝ × ℝ => S.initial p.1 e) := (S.initial_continuous e).comp continuous_fst
  exact sineSlope_continuous.comp (continuous_fst.prodMk (hi.fst.prodMk (hi.snd.prodMk continuous_snd)))

theorem RobinShootingData.residual_continuous (S : RobinShootingData n) : Continuous S.residual := by
  have hi := S.initial_continuous (Fin.last n)
  have hin : Continuous (fun k : ℝ =>
      (k, (S.initial k (Fin.last n)).1, (S.initial k (Fin.last n)).2, S.gap (Fin.last n))) :=
    continuous_id.prodMk (hi.fst.prodMk (hi.snd.prodMk continuous_const))
  unfold residual slope value
  exact (sineSlope_continuous.comp hin).add
    (continuous_const.mul (sineValue_continuous.comp hin))

theorem RobinShootingData.initial_ne_zero (S : RobinShootingData n) (k : ℝ) (e : Fin (n + 1)) :
    S.initial k e ≠ (0, 0) := by
  induction e using Fin.induction with
  | zero => simp [S.initial_zero]
  | succ i ih =>
    rw [S.initial_succ]
    exact reactionJump_ne_zero _ (sineFlow_ne_zero _ _ ih)

theorem RobinShootingData.value_slope_ne_zero (S : RobinShootingData n) (k : ℝ) (e : Fin (n + 1)) (x : ℝ) :
    (S.value k e x, S.slope k e x) ≠ (0, 0) :=
  sineFlow_ne_zero k x (S.initial_ne_zero k e)

theorem RobinShootingData.initial_zero_parameter_sign (S : RobinShootingData n) (e : Fin (n + 1)) :
    0 < (S.initial 0 e).1 ∧ 0 ≤ (S.initial 0 e).2 := by
  induction e using Fin.induction with
  | zero => exact ⟨zero_lt_one, S.leftRate_nonneg⟩
  | succ i ih =>
    rw [S.initial_succ, sineFlow_zero_parameter]
    change 0 < (S.initial 0 i.castSucc).1 + (S.initial 0 i.castSucc).2 * S.gap i.castSucc ∧
      0 ≤ (S.initial 0 i.castSucc).2 + S.reaction i *
        ((S.initial 0 i.castSucc).1 + (S.initial 0 i.castSucc).2 * S.gap i.castSucc)
    have hv := add_pos_of_pos_of_nonneg ih.1 (mul_nonneg ih.2 (S.gap_pos i.castSucc).le)
    exact ⟨hv, add_nonneg ih.2 (mul_pos (S.reaction_pos i) hv).le⟩

theorem RobinShootingData.zero_parameter_positive (S : RobinShootingData n) (e : Fin (n + 1))
    {x : ℝ} (hx : 0 ≤ x) : 0 < S.value 0 e x := by
  rw [value, sineValue_zero_parameter]
  have h := S.initial_zero_parameter_sign e
  exact add_pos_of_pos_of_nonneg h.1 (mul_nonneg h.2 hx)

theorem RobinShootingData.zero_parameter_slope_succ (S : RobinShootingData n) (i : Fin n) :
    0 < (S.initial 0 i.succ).2 := by
  rw [S.initial_succ, sineFlow_zero_parameter]
  have h := S.initial_zero_parameter_sign i.castSucc
  change 0 < (S.initial 0 i.castSucc).2 + S.reaction i *
    ((S.initial 0 i.castSucc).1 + (S.initial 0 i.castSucc).2 * S.gap i.castSucc)
  exact add_pos_of_nonneg_of_pos h.2 (mul_pos (S.reaction_pos i)
    (add_pos_of_pos_of_nonneg h.1 (mul_nonneg h.2 (S.gap_pos i.castSucc).le)))

theorem RobinShootingData.final_slope_zero_pos (S : RobinShootingData n) (hn : 0 < n) :
    0 < S.slope 0 (Fin.last n) (S.gap (Fin.last n)) := by
  unfold slope
  rw [sineSlope_zero_parameter]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact S.zero_parameter_slope_succ (Fin.last m)

theorem RobinShootingData.residual_zero_pos (S : RobinShootingData n) (hn : 0 < n) :
    0 < S.residual 0 :=
  add_pos_of_pos_of_nonneg (S.final_slope_zero_pos hn)
    (mul_nonneg S.rightRate_nonneg
      (S.zero_parameter_positive (Fin.last n) (S.gap_pos (Fin.last n)).le).le)

theorem RobinShootingData.first_gap_negative (S : RobinShootingData n) :
    S.value (Real.pi / S.gap 0) 0 (S.gap 0) = -1 := by
  unfold value
  rw [S.initial_zero]
  have he : Real.pi / S.gap 0 * S.gap 0 = Real.pi :=
    div_mul_cancel₀ _ (ne_of_gt (S.gap_pos 0))
  have hk : Real.pi / S.gap 0 ≠ 0 := ne_of_gt (div_pos Real.pi_pos (S.gap_pos 0))
  rw [sineValue_of_ne_zero hk, he, Real.cos_pi, Real.sin_pi]
  ring

end TimeTraps.Spectral
