module

public import TimeTraps.Spectral.TangentEquationRemainder
public import TimeTraps.Spectral.DimensionlessRootLimits

@[expose] public section

/-! Rigorous series inversion for the dimensionless spectral equation. -/

namespace TimeTraps.Spectral

open Set Filter Topology Asymptotics

theorem phase_inverse_residual :
    (fun z : ℝ => z ^ 2 -
      (z * Real.tan z - (z * Real.tan z) ^ 2 / 3 + 4 * (z * Real.tan z) ^ 3 / 45))
      =O[𝓝 0] (fun z => z ^ 8) := by
  let A : ℝ → ℝ := fun z => z * Real.tan z
  let P : ℝ → ℝ := fun z => z ^ 2 + z ^ 4 / 3 + 2 * z ^ 6 / 15
  let Q : ℝ → ℝ := fun z => 1 / 27 - 8 * z ^ 2 / 225 - 128 * z ^ 4 / 6075 -
    88 * z ^ 6 / 10125 - 16 * z ^ 8 / 10125 - 32 * z ^ 10 / 151875
  have hA : ContinuousAt A 0 :=
    continuousAt_id.mul (Real.continuousAt_tan.mpr (by simp))
  have hP : ContinuousAt P 0 := by dsimp [P]; fun_prop
  have hQ : ContinuousAt Q 0 := by dsimp [Q]; fun_prop
  have hfac : ContinuousAt (fun z =>
      1 - (A z + P z) / 3 + 4 * (A z ^ 2 + A z * P z + P z ^ 2) / 45) 0 := by
    fun_prop
  have hr : (fun z => (A z - P z) *
      (1 - (A z + P z) / 3 + 4 * (A z ^ 2 + A z * P z + P z ^ 2) / 45))
      =O[𝓝 0] (fun z => z ^ 8) := by
    simpa only [mul_one] using phase_product_taylor_remainder.mul hfac.isBigO
  have hp : (fun z => z ^ 8 * Q z) =O[𝓝 0] (fun z => z ^ 8) := by
    simpa only [mul_one] using (isBigO_refl (fun z : ℝ => z ^ 8) (𝓝 0)).mul hQ.isBigO
  exact (hp.sub hr).congr_left (fun z => by dsimp [A, P, Q]; ring)

/-- The remainder is controlled by the fourth power of the exact parameter,
not by an assumed approximation to the root. -/
theorem budgetPhase_eighth_power_isBigO :
    (fun a : ℝ => budgetPhase a ^ 8) =O[𝓝[>] 0] (fun a => a ^ 4) := by
  apply IsBigO.of_bound 1
  filter_upwards [self_mem_nhdsWithin] with a ha
  change 0 < a at ha
  have hs : budgetPhase a ^ 2 ≤ a := (budgetPhase_sq_lt ha).le
  have hpow : (budgetPhase a ^ 2) ^ 4 ≤ a ^ 4 :=
    pow_le_pow_left₀ (sq_nonneg _) hs 4
  simpa [Real.norm_eq_abs, abs_of_nonneg (budgetPhase_nonneg a),
    abs_of_pos ha, ← pow_mul] using hpow

theorem budgetPhase_inverse_expansion :
    (fun a : ℝ => budgetPhase a ^ 2 - (a - a ^ 2 / 3 + 4 * a ^ 3 / 45))
      =O[𝓝[>] 0] (fun a => a ^ 4) := by
  have h := (phase_inverse_residual.comp_tendsto budgetPhase_tendsto_zero)
    |>.trans budgetPhase_eighth_power_isBigO
  apply h.congr'
  · filter_upwards [self_mem_nhdsWithin] with a ha
    simp only [Function.comp_apply, budgetPhase_equation ha]
  · exact Eventually.of_forall (fun _ => rfl)

end TimeTraps.Spectral
