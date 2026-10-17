module

public import TimeTraps.Spectral.TangentTaylorRemainder

@[expose] public section

/-! Quotient algebra with analytic remainders: tan z through degree five. -/

namespace TimeTraps.Spectral

open Set Filter Topology Asymptotics

theorem tangent_taylor_remainder :
    (fun z : ℝ => Real.tan z - (z + z ^ 3 / 3 + 2 * z ^ 5 / 15))
      =O[𝓝 0] (fun z => z ^ 7) := by
  have hP : (fun z : ℝ => z + z ^ 3 / 3 + 2 * z ^ 5 / 15) =O[𝓝 0] (fun z => z) := by
    have hc : ContinuousAt (fun z : ℝ => 1 + z ^ 2 / 3 + 2 * z ^ 4 / 15) 0 := by fun_prop
    exact ((isBigO_refl (fun z : ℝ => z) (𝓝 0)).mul hc.isBigO).congr
      (fun z => by ring) (fun z => by ring)
  have hc : (fun z : ℝ => (z + z ^ 3 / 3 + 2 * z ^ 5 / 15) *
      (Real.cos z - (1 - z ^ 2 / 2 + z ^ 4 / 24))) =O[𝓝 0] (fun z => z ^ 7) := by
    exact (hP.mul cosine_taylor_remainder).congr_right (fun z => by ring)
  have hp : (fun z : ℝ => z ^ 7 * (19 / 360 - z ^ 2 / 180)) =O[𝓝 0] (fun z => z ^ 7) := by
    have hh : ContinuousAt (fun z : ℝ => 19 / 360 - z ^ 2 / 180) 0 := by fun_prop
    simpa using (isBigO_refl (fun z : ℝ => z ^ 7) (𝓝 0)).mul hh.isBigO
  have hs : (fun z : ℝ => Real.sin z - (z + z ^ 3 / 3 + 2 * z ^ 5 / 15) * Real.cos z)
      =O[𝓝 0] (fun z => z ^ 7) := by
    exact ((sine_taylor_remainder.sub hc).add hp).congr_left (fun z => by ring)
  have hi : (fun z : ℝ => (Real.cos z)⁻¹) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
    (Real.continuous_cos.continuousAt.inv₀ (by simp)).isBigO
  have h := hs.mul hi
  apply h.congr'
  · filter_upwards [Real.continuous_cos.continuousAt.eventually_ne
      (by simp : Real.cos (0 : ℝ) ≠ 0)] with z hz
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hz]
  · exact Eventually.of_forall (fun z => mul_one _)

theorem phase_product_taylor_remainder :
    (fun z : ℝ => z * Real.tan z - (z ^ 2 + z ^ 4 / 3 + 2 * z ^ 6 / 15))
      =O[𝓝 0] (fun z => z ^ 8) := by
  exact ((isBigO_refl (fun z : ℝ => z) (𝓝 0)).mul tangent_taylor_remainder).congr
    (fun z => by ring) (fun z => by ring)

end TimeTraps.Spectral
