module

public import TimeTraps.Probability.BrownianIntegralElementaryData

@[expose] public section

/-! Elementary left-adapted L² processes and their actual L² stochastic
increments. The equality of Gram pairings is representation independent. -/

namespace TimeTraps.Probability.BrownianIntegralElementary

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

theorem coefficient_measurable (a : BrownianIntegralElementary B hBm P) :
    Measurable a.coefficient :=
  (a.adapted.mono ((brownianNaturalFiltration B hBm).le a.left)).measurable

theorem process_memLp (a : BrownianIntegralElementary B hBm P) :
    MemLp (brownianElementaryProcess a.left a.right a.coefficient) 2 (volume.prod P) :=
  brownianElementaryProcess_memLp a.left a.right a.coefficient_measurable a.squareIntegrable

theorem increment_memLp (hB : IsPreBrownianReal B P) (a : BrownianIntegralElementary B hBm P) :
    MemLp (fun ω => a.coefficient ω * (B a.right ω - B a.left ω)) 2 P :=
  brownian_weighted_increment_memLp hB hBm a.ordered a.adapted a.squareIntegrable

noncomputable def processL2 (a : BrownianIntegralElementary B hBm P) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
  a.process_memLp.toLp (brownianElementaryProcess a.left a.right a.coefficient)

noncomputable def integralL2 (hB : IsPreBrownianReal B P) (a : BrownianIntegralElementary B hBm P) :
    Lp ℝ 2 P := (a.increment_memLp hB).toLp
      (fun ω => a.coefficient ω * (B a.right ω - B a.left ω))

theorem processL2_coe (a : BrownianIntegralElementary B hBm P) :
    a.processL2 =ᵐ[volume.prod P] brownianElementaryProcess a.left a.right a.coefficient :=
  a.process_memLp.coeFn_toLp

theorem integralL2_coe (hB : IsPreBrownianReal B P) (a : BrownianIntegralElementary B hBm P) :
    a.integralL2 hB =ᵐ[P] fun ω => a.coefficient ω * (B a.right ω - B a.left ω) :=
  (a.increment_memLp hB).coeFn_toLp

theorem processL2_inner [SFinite P] (a b : BrownianIntegralElementary B hBm P) :
    inner ℝ a.processL2 b.processL2 = brownianIntervalOverlap a.left a.right b.left b.right *
      ∫ ω, a.coefficient ω * b.coefficient ω ∂P := by
  calc
    _ = ∫ p, brownianElementaryProcess a.left a.right a.coefficient p *
        brownianElementaryProcess b.left b.right b.coefficient p ∂volume.prod P := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [a.processL2_coe, b.processL2_coe] with p ha hb
      rw [Real.inner_apply, ha, hb]
    _ = _ := brownianElementaryProcess_pairing _ _ _ _ _ _

theorem integralL2_inner (hB : IsPreBrownianReal B P) (a b : BrownianIntegralElementary B hBm P) :
    inner ℝ (a.integralL2 hB) (b.integralL2 hB) =
      brownianIntervalOverlap a.left a.right b.left b.right *
        ∫ ω, a.coefficient ω * b.coefficient ω ∂P := by
  calc
    _ = ∫ ω, (a.coefficient ω * (B a.right ω - B a.left ω)) *
        (b.coefficient ω * (B b.right ω - B b.left ω)) ∂P := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [a.integralL2_coe hB, b.integralL2_coe hB] with ω ha hb
      rw [Real.inner_apply, ha, hb]
    _ = _ := brownian_weighted_increment_covariance hB hBm a.ordered b.ordered
      a.adapted b.adapted a.squareIntegrable b.squareIntegrable

theorem gram_eq (hB : IsPreBrownianReal B P) (a b : BrownianIntegralElementary B hBm P) :
    inner ℝ a.processL2 b.processL2 = inner ℝ (a.integralL2 hB) (b.integralL2 hB) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [a.processL2_inner b, a.integralL2_inner hB b]

theorem processL2_norm_sq [SFinite P] (a : BrownianIntegralElementary B hBm P) :
    ‖a.processL2‖ ^ 2 = (a.right.val - a.left.val) * ∫ ω, a.coefficient ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, a.processL2_inner a]
  have hnonneg : 0 ≤ a.right.val - a.left.val := sub_nonneg.mpr a.ordered
  simp only [brownianIntervalOverlap, min_self, max_self, max_eq_left hnonneg, pow_two]

end TimeTraps.Probability.BrownianIntegralElementary
