module

public import TimeTraps.Probability.BrownianIntegralFourthCompact
public import TimeTraps.Probability.BrownianIntegralFourthCountable
public import TimeTraps.Probability.BrownianCountableIntegrandCutoff

@[expose] public section

/-! Actual compact-time fourth-energy inequality for a bounded Borel
spatial coefficient continuous off a countable set. The coefficient class
includes the reflected Tanaka sign differences used below. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {g : ℝ → ℝ} {C : Set ℝ} {M : ℝ≥0}

theorem brownianCountableIntegrand_process_memLp_four
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T t : ℝ≥0) :
    MemLp (brownianStochasticIntegralProcess
      (brownianCountableIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable hg hb hC hc T) t) 4 brownianDyadicMeasure := by
  have he := brownianIntegralProcess_ae brownianDyadicPath_isPreBrownianReal
    (brownianCountableIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable hg hb hC hc T) t
  rw [brownianCountableIntegral_upTo] at he
  exact (brownianCountableIntegral_fourth_energy brownianDyadicPath_isBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable hg hb hC hc (min t T)).1.ae_eq he.symm

theorem brownianCountableIntegral_compact_fourth_energy
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T : ℝ≥0) :
    MemLp (fun ω => ‖brownianIntegralContinuousL2 T
      (brownianCountableIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable hg hb hC hc T) ω‖) 4 brownianDyadicMeasure ∧
    (∫ ω, ‖brownianIntegralContinuousL2 T
      (brownianCountableIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable hg hb hC hc T) ω‖ ^ 4 ∂brownianDyadicMeasure) ≤
      600 * ∫ ω, (∫ r in (0 : ℝ)..T.val, g (brownianDyadicPath r.toNNReal ω) ^ 2) ^ 2
        ∂brownianDyadicMeasure := by
  let f := brownianCountableIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable hg hb hC hc T
  have hm := brownianIntegralCompactNorm_fourth T f
    (fun t _ => brownianCountableIntegrand_process_memLp_four hg hb hC hc T t)
  have he := brownianIntegralProcess_ae brownianDyadicPath_isPreBrownianReal f T
  change brownianStochasticIntegralProcess f T =ᵐ[brownianDyadicMeasure]
    brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal T
      (brownianCountableIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable hg hb hC hc T) at he
  rw [brownianCountableIntegral_upTo, min_self] at he
  have hei := integral_congr_ae (he.mono (fun _ h => congrArg (fun z : ℝ => z ^ 4) h))
  rw [hei] at hm
  have hbnd := brownianCountableIntegral_fourth_energy_literal brownianDyadicPath_isBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable hg hb hC hc T
  refine ⟨hm.1, hm.2.trans ?_⟩
  convert mul_le_mul_of_nonneg_left hbnd (by norm_num : (0 : ℝ) ≤ 4) using 1
  ring

end TimeTraps.Probability
