module

public import TimeTraps.Probability.BrownianIntegralMartingale

@[expose] public section

/-! An explicit path representative for one elementary integral. Equality
with the cutoff integral and chosen martingale is asserted separately at
each fixed time. Continuity holds on the original Brownian path event. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

def BrownianIntegralElementary.integralPath (a : BrownianIntegralElementary B hBm P)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  a.coefficient ω * (B (min t a.right) ω - B (min t a.left) ω)

theorem BrownianIntegralElementary.integralPath_before_left
    (a : BrownianIntegralElementary B hBm P) {t : ℝ≥0} (ht : t ≤ a.left) :
    a.integralPath t = 0 := by
  funext ω
  simp only [integralPath, min_eq_left ht, min_eq_left (ht.trans a.ordered), sub_self, mul_zero,
    Pi.zero_apply]

theorem BrownianIntegralElementary.integralPath_continuous
    (a : BrownianIntegralElementary B hBm P) {ω : Ω}
    (hω : Continuous (fun t => B t ω)) : Continuous (fun t => a.integralPath t ω) :=
  continuous_const.mul ((hω.comp (continuous_id.min continuous_const)).sub
    (hω.comp (continuous_id.min continuous_const)))

theorem BrownianIntegralElementary.integralPath_measurable
    (a : BrownianIntegralElementary B hBm P) (t : ℝ≥0) : Measurable (a.integralPath t) :=
  a.coefficient_measurable.mul ((hBm (min t a.right)).sub (hBm (min t a.left)))

theorem BrownianIntegralElementary.integralPath_jointly_measurable
    (a : BrownianIntegralElementary B hBm P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) :
    Measurable (fun p : ℝ≥0 × Ω => a.integralPath p.1 p.2) :=
  (a.coefficient_measurable.comp measurable_snd).mul
    ((hjoint.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)).sub
      (hjoint.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)))

theorem BrownianIntegralElementary.integralPath_stronglyAdapted
    (a : BrownianIntegralElementary B hBm P) :
    StronglyAdapted (brownianNaturalFiltration B hBm) a.integralPath := by
  intro t
  by_cases ht : a.left ≤ t
  · exact (a.adapted.mono ((brownianNaturalFiltration B hBm).mono ht)).mul
      (((brownianNaturalFiltration_stronglyAdapted B hBm (min t a.right)).mono
          ((brownianNaturalFiltration B hBm).mono (min_le_left t a.right))).sub
        ((brownianNaturalFiltration_stronglyAdapted B hBm (min t a.left)).mono
          ((brownianNaturalFiltration B hBm).mono (min_le_left t a.left))))
  · rw [a.integralPath_before_left (le_of_not_ge ht)]
    exact stronglyMeasurable_zero

theorem BrownianIntegralElementary.integralPath_integralUpTo_ae
    (a : BrownianIntegralElementary B hBm P) (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    a.integralPath t =ᵐ[P] brownianIntegralUpTo hB t (brownianIntegralGenerator a) := by
  change a.integralPath t =ᵐ[P]
    brownianIntegral hB (brownianTimeCutoff B hBm P t (brownianIntegralGenerator a))
  by_cases ht : a.left ≤ t
  · rw [brownianTimeCutoff_generator a ht, brownianIntegral_generator]
    have h := (a.refineLeft (min a.right t) (le_min a.ordered ht)).integralL2_coe hB
    have he : a.integralPath t = fun ω => a.coefficient ω * (B (min a.right t) ω - B a.left ω) := by
      funext ω
      simp only [integralPath, min_eq_right ht, min_comm t a.right]
    rw [he]
    exact h.symm
  · rw [brownianTimeCutoff_generator_zero a (le_of_not_ge ht), map_zero,
      a.integralPath_before_left (le_of_not_ge ht)]
    exact (Lp.coeFn_zero ℝ 2 P).symm

theorem BrownianIntegralElementary.integralPath_martingale_ae
    (a : BrownianIntegralElementary B hBm P) (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    a.integralPath t =ᵐ[P] brownianIntegralProcess hB (brownianIntegralGenerator a) t :=
  (a.integralPath_integralUpTo_ae hB t).trans
    (brownianIntegralProcess_ae hB (brownianIntegralGenerator a) t).symm

theorem BrownianIntegralElementary.integralPath_martingale
    (a : BrownianIntegralElementary B hBm P) (hB : IsPreBrownianReal B P) :
    Martingale a.integralPath (brownianNaturalFiltration B hBm) P :=
  (brownianIntegralProcess_martingale hB (brownianIntegralGenerator a)).congr
    a.integralPath_stronglyAdapted (fun t => (a.integralPath_martingale_ae hB t).symm)

theorem BrownianIntegralElementary.integralPath_continuous_ae
    (a : BrownianIntegralElementary B hBm P) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Continuous (fun t => a.integralPath t ω) :=
  hB.cont.mono (fun _ hω => a.integralPath_continuous hω)

end TimeTraps.Probability
