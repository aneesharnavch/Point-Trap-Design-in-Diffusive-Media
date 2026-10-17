module

public import TimeTraps.Probability.ReflectedBackwardHeatData

@[expose] public section

/-! Actual backward heat martingales for every continuous terminal
observable. Conditional evolution uses the original Brownian past and the
checked reflected semigroup composition. This literal, bounded process
has continuous paths on the Brownian continuity event. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem reflectedBackwardHeat_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) :
    P[reflectedBackwardHeat B L hL D x f T t | brownianNaturalFiltration B hBm s] =ᵐ[P]
      reflectedBackwardHeat B L hL D x f T s := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  by_cases hsT : s ≤ T
  · have hsv : s ≤ min t T := le_min hst hsT
    have hvT : (min t T).val ≤ T.val := min_le_right t T
    have hc := reflectedContinuousInput_condExp hB hBm L hL D hD x
      (reflectedFellerTimeOperator L hL D (T.val - (min t T).val) f) hsv
    have he : reflectedFellerTimeOperator L hL D ((min t T).val - s.val)
        (reflectedFellerTimeOperator L hL D (T.val - (min t T).val) f) =
        reflectedFellerTimeOperator L hL D (T.val - s.val) f := by
      rw [reflectedFellerTimeOperator_comp_nonneg L hL D hD.le
        (sub_nonneg.mpr hsv) (sub_nonneg.mpr hvT)]
      have htime : (min t T).val - s.val + (T.val - (min t T).val) = T.val - s.val := by ring
      rw [htime]
    change P[fun ω => reflectedContinuousInput L hL D x
      (reflectedFellerTimeOperator L hL D (T.val - (min t T).val) f) (B (min t T) ω) |
      brownianNaturalFiltration B hBm s] =ᵐ[P]
        (fun ω => reflectedContinuousInput L hL D x
          (reflectedFellerTimeOperator L hL D (T.val - (min s T).val) f) (B (min s T) ω))
    rw [min_eq_left hsT]
    simpa only [he] using hc
  · have hTs : T ≤ s := (lt_of_not_ge hsT).le
    have he : reflectedBackwardHeat B L hL D x f T t =
        reflectedBackwardHeat B L hL D x f T s := by
      funext ω
      exact (reflectedBackwardHeat_after_horizon B L hL D x f (hTs.trans hst) ω).trans
        (reflectedBackwardHeat_after_horizon B L hL D x f hTs ω).symm
    rw [he]
    exact condExp_of_aestronglyMeasurable' ((brownianNaturalFiltration B hBm).le s)
      (reflectedBackwardHeat_stronglyAdapted B hBm L hL D x f T s).aestronglyMeasurable
      ((reflectedBackwardHeat_memLp B hBm L hL D x f T s).integrable (by norm_num))

theorem reflectedBackwardHeat_martingale (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    Martingale (reflectedBackwardHeat B L hL D x f T) (brownianNaturalFiltration B hBm) P :=
  ⟨reflectedBackwardHeat_stronglyAdapted B hBm L hL D x f T,
    fun _ _ hst => reflectedBackwardHeat_condExp hB hBm L hL D hD x f T hst⟩

theorem reflectedBackwardHeat_continuous_ae (hB : IsBrownianReal B P)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, Continuous (fun t => reflectedBackwardHeat B L hL D x f T t ω) := by
  filter_upwards [hB.cont] with ω hω
  exact reflectedBackwardHeat_continuous B L hL D x f T ω hω

theorem brownianDyadic_reflectedBackwardHeat_martingale
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    Martingale (reflectedBackwardHeat brownianDyadicPath L hL D x f T)
      brownianFiltration brownianDyadicMeasure ∧
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) =>
      reflectedBackwardHeat brownianDyadicPath L hL D x f T p.1 p.2) ∧
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Continuous (fun t => reflectedBackwardHeat brownianDyadicPath L hL D x f T t ω) :=
  ⟨reflectedBackwardHeat_martingale brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable L hL D hD x f T,
    reflectedBackwardHeat_jointly_measurable brownianDyadicPath brownianDyadicPath_jointly_measurable
      L hL D x f T,
    reflectedBackwardHeat_continuous_ae brownianDyadicPath_isBrownianReal L hL D x f T⟩

end TimeTraps.Probability
