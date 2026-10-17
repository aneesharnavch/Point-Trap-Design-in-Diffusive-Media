module

public import TimeTraps.Probability.SampledFourthMomentTail
public import Mathlib.Analysis.Normed.Group.InfiniteSum

@[expose] public section

/-! Geometric second-moment bounds give summable exceedance
probabilities. Finitely many uncontrolled initial indices are harmless. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped ENNReal

variable {Ω B : Type*} [MeasurableSpace Ω] [NormedAddCommGroup B]
variable {μ : Measure Ω} [IsFiniteMeasure μ]

theorem secondMoment_norm_tail {f : Ω → B} {M ε : ℝ}
    (hi : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hb : (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤ M) (hε : 0 < ε) :
    μ.real {ω | ε < ‖f ω‖} ≤ M / ε ^ 2 := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => ‖f ω‖ ^ 2)
    (Eventually.of_forall (fun _ => sq_nonneg _)) hi (ε ^ 2)
  have he : {ω | ε ^ 2 ≤ ‖f ω‖ ^ 2} = {ω | ε ≤ ‖f ω‖} := by
    ext ω
    exact sq_le_sq₀ hε.le (norm_nonneg _)
  rw [he] at h
  have hm : μ.real {ω | ε < ‖f ω‖} ≤ μ.real {ω | ε ≤ ‖f ω‖} :=
    measureReal_mono (fun ω (hω : ε < ‖f ω‖) => (show ε ≤ ‖f ω‖ from hω.le))
  exact hm.trans ((le_div_iff₀ (sq_pos_of_pos hε)).mpr (by nlinarith [h.trans hb]))

theorem geometric_secondMoment_tail {f : ℕ → Ω → B} {C : ℝ} (n : ℕ)
    (hi : Integrable (fun ω => ‖f n ω‖ ^ 2) μ)
    (hb : (∫ ω, ‖f n ω‖ ^ 2 ∂μ) ≤ C * (1 / 16 : ℝ) ^ n) :
    μ.real {ω | (1 / 2 : ℝ) ^ n < ‖f n ω‖} ≤ C * (1 / 4 : ℝ) ^ n := by
  have h := secondMoment_norm_tail hi hb (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
  convert h using 1
  rw [pow_right_comm (1 / 2 : ℝ) n 2, mul_div_assoc, ← div_pow]
  norm_num

theorem geometric_secondMoment_exceedance_summable {f : ℕ → Ω → B} {C : ℝ}
    (hi : ∀ n, Integrable (fun ω => ‖f n ω‖ ^ 2) μ)
    (hb : ∀ᶠ n in atTop, (∫ ω, ‖f n ω‖ ^ 2 ∂μ) ≤ C * (1 / 16 : ℝ) ^ n) :
    (∑' n, μ {ω | (1 / 2 : ℝ) ^ n < ‖f n ω‖}) ≠ ∞ := by
  have hgeom := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left C
  have hs : Summable (fun n => μ.real {ω | (1 / 2 : ℝ) ^ n < ‖f n ω‖}) := by
    apply hgeom.of_norm_bounded_eventually_nat
    filter_upwards [hb] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact geometric_secondMoment_tail n (hi n) hn
  have he (n : ℕ) : ENNReal.ofReal (μ.real {ω | (1 / 2 : ℝ) ^ n < ‖f n ω‖}) =
      μ {ω | (1 / 2 : ℝ) ^ n < ‖f n ω‖} := ENNReal.ofReal_toReal (measure_ne_top _ _)
  simpa only [he] using hs.tsum_ofReal_ne_top

end TimeTraps.Probability
