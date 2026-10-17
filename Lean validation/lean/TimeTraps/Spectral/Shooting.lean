module

public import TimeTraps.Spectral.SineFlow
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
Exact normalized shooting on independently prescribed positive gaps and
positive reaction jumps q_i = κ_i/D. The initial value is one and the initial
derivative is zero. No right boundary condition or positivity is assumed.
-/

namespace TimeTraps.Spectral

open Set

structure ShootingData (n : ℕ) where
  gap : Fin (n + 1) → ℝ
  gap_pos : ∀ e, 0 < gap e
  reaction : Fin n → ℝ
  reaction_pos : ∀ i, 0 < reaction i

variable {n : ℕ}

noncomputable def ShootingData.initial (S : ShootingData n) (k : ℝ) : Fin (n + 1) → ℝ × ℝ :=
  Fin.induction (1, 0) (fun i p => reactionJump (S.reaction i) (sineFlow k (S.gap i.castSucc) p))

noncomputable def ShootingData.value (S : ShootingData n) (k : ℝ) (e : Fin (n + 1)) (x : ℝ) : ℝ :=
  sineValue k (S.initial k e).1 (S.initial k e).2 x

noncomputable def ShootingData.slope (S : ShootingData n) (k : ℝ) (e : Fin (n + 1)) (x : ℝ) : ℝ :=
  sineSlope k (S.initial k e).1 (S.initial k e).2 x

noncomputable def ShootingData.residual (S : ShootingData n) (k : ℝ) : ℝ :=
  S.slope k (Fin.last n) (S.gap (Fin.last n))

theorem ShootingData.initial_zero (S : ShootingData n) (k : ℝ) : S.initial k 0 = (1, 0) := rfl

theorem ShootingData.initial_succ (S : ShootingData n) (k : ℝ) (i : Fin n) :
    S.initial k i.succ = reactionJump (S.reaction i) (sineFlow k (S.gap i.castSucc) (S.initial k i.castSucc)) := rfl

theorem ShootingData.value_start (S : ShootingData n) (k : ℝ) (e : Fin (n + 1)) :
    S.value k e 0 = (S.initial k e).1 := by simp [value, sineValue]

theorem ShootingData.slope_start (S : ShootingData n) (k : ℝ) (e : Fin (n + 1)) :
    S.slope k e 0 = (S.initial k e).2 := by simp [slope, sineSlope]

theorem ShootingData.left_value (S : ShootingData n) (k : ℝ) : S.value k 0 0 = 1 := by
  rw [S.value_start, S.initial_zero]

theorem ShootingData.left_slope (S : ShootingData n) (k : ℝ) : S.slope k 0 0 = 0 := by
  rw [S.slope_start, S.initial_zero]

theorem ShootingData.value_matching (S : ShootingData n) (k : ℝ) (i : Fin n) :
    S.value k i.succ 0 = S.value k i.castSucc (S.gap i.castSucc) := by
  rw [S.value_start, S.initial_succ]
  rfl

theorem ShootingData.slope_jump (S : ShootingData n) (k : ℝ) (i : Fin n) :
    S.slope k i.succ 0 = S.slope k i.castSucc (S.gap i.castSucc) +
      S.reaction i * S.value k i.castSucc (S.gap i.castSucc) := by
  rw [S.slope_start, S.initial_succ]
  rfl

theorem ShootingData.value_hasDerivAt (S : ShootingData n) (k : ℝ) (e : Fin (n + 1)) (x : ℝ) :
    HasDerivAt (S.value k e) (S.slope k e x) x := sineValue_hasDerivAt _ _ _ _

theorem ShootingData.slope_hasDerivAt (S : ShootingData n) (k : ℝ) (e : Fin (n + 1)) (x : ℝ) :
    HasDerivAt (S.slope k e) (-(k ^ 2) * S.value k e x) x := sineSlope_hasDerivAt _ _ _ _

theorem ShootingData.initial_continuous (S : ShootingData n) (e : Fin (n + 1)) :
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

theorem ShootingData.value_continuous (S : ShootingData n) (e : Fin (n + 1)) :
    Continuous (fun p : ℝ × ℝ => S.value p.1 e p.2) := by
  have hi : Continuous (fun p : ℝ × ℝ => S.initial p.1 e) := (S.initial_continuous e).comp continuous_fst
  exact sineValue_continuous.comp (continuous_fst.prodMk (hi.fst.prodMk (hi.snd.prodMk continuous_snd)))

theorem ShootingData.slope_continuous (S : ShootingData n) (e : Fin (n + 1)) :
    Continuous (fun p : ℝ × ℝ => S.slope p.1 e p.2) := by
  have hi : Continuous (fun p : ℝ × ℝ => S.initial p.1 e) := (S.initial_continuous e).comp continuous_fst
  exact sineSlope_continuous.comp (continuous_fst.prodMk (hi.fst.prodMk (hi.snd.prodMk continuous_snd)))

theorem ShootingData.residual_continuous (S : ShootingData n) : Continuous S.residual := by
  have hi : Continuous (fun k : ℝ => (k, S.gap (Fin.last n))) := continuous_id.prodMk continuous_const
  have h := (S.slope_continuous (Fin.last n)).comp hi
  exact h

theorem ShootingData.initial_ne_zero (S : ShootingData n) (k : ℝ) (e : Fin (n + 1)) :
    S.initial k e ≠ (0, 0) := by
  induction e using Fin.induction with
  | zero => simp [S.initial_zero]
  | succ i ih =>
    rw [S.initial_succ]
    exact reactionJump_ne_zero _ (sineFlow_ne_zero _ _ ih)

theorem ShootingData.value_slope_ne_zero (S : ShootingData n) (k : ℝ) (e : Fin (n + 1)) (x : ℝ) :
    (S.value k e x, S.slope k e x) ≠ (0, 0) :=
  sineFlow_ne_zero k x (S.initial_ne_zero k e)

theorem ShootingData.initial_zero_parameter_sign (S : ShootingData n) (e : Fin (n + 1)) :
    0 < (S.initial 0 e).1 ∧ 0 ≤ (S.initial 0 e).2 := by
  induction e using Fin.induction with
  | zero => simp [S.initial_zero]
  | succ i ih =>
    rw [S.initial_succ, sineFlow_zero_parameter]
    change 0 < (S.initial 0 i.castSucc).1 + (S.initial 0 i.castSucc).2 * S.gap i.castSucc ∧
      0 ≤ (S.initial 0 i.castSucc).2 + S.reaction i *
        ((S.initial 0 i.castSucc).1 + (S.initial 0 i.castSucc).2 * S.gap i.castSucc)
    have hv := add_pos_of_pos_of_nonneg ih.1 (mul_nonneg ih.2 (S.gap_pos i.castSucc).le)
    exact ⟨hv, add_nonneg ih.2 (mul_pos (S.reaction_pos i) hv).le⟩

theorem ShootingData.zero_parameter_positive (S : ShootingData n) (e : Fin (n + 1))
    {x : ℝ} (hx : 0 ≤ x) : 0 < S.value 0 e x := by
  rw [value, sineValue_zero_parameter]
  have h := S.initial_zero_parameter_sign e
  exact add_pos_of_pos_of_nonneg h.1 (mul_nonneg h.2 hx)

theorem ShootingData.zero_parameter_slope_succ (S : ShootingData n) (i : Fin n) :
    0 < (S.initial 0 i.succ).2 := by
  rw [S.initial_succ, sineFlow_zero_parameter]
  have h := S.initial_zero_parameter_sign i.castSucc
  change 0 < (S.initial 0 i.castSucc).2 + S.reaction i *
    ((S.initial 0 i.castSucc).1 + (S.initial 0 i.castSucc).2 * S.gap i.castSucc)
  exact add_pos_of_nonneg_of_pos h.2 (mul_pos (S.reaction_pos i)
    (add_pos_of_pos_of_nonneg h.1 (mul_nonneg h.2 (S.gap_pos i.castSucc).le)))

theorem ShootingData.residual_zero_pos (S : ShootingData n) (hn : 0 < n) : 0 < S.residual 0 := by
  unfold residual slope
  rw [sineSlope_zero_parameter]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact S.zero_parameter_slope_succ (Fin.last m)

theorem ShootingData.first_gap_zero (S : ShootingData n) :
    S.value (Real.pi / (2 * S.gap 0)) 0 (S.gap 0) = 0 := by
  unfold value
  rw [S.initial_zero]
  simp only [sineValue, zero_mul, one_mul, add_zero]
  have he : Real.pi / (2 * S.gap 0) * S.gap 0 = Real.pi / 2 := by
    field_simp [ne_of_gt (S.gap_pos 0)]
  rw [he, Real.cos_pi_div_two]

end TimeTraps.Spectral
