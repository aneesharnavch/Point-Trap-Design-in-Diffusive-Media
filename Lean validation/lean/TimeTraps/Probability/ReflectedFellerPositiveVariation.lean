module

public import TimeTraps.Probability.ReflectedFellerCurvatureContinuity

@[expose] public section

/-! Exact positive-time evolution identities for every continuous
initial function. Curvature propagates by the actual semigroup, and
ordinary C-valued integration gives the variation between any two
positive times, with no initial-domain assumption. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped Topology

theorem reflectedFellerCurvatureCurve_semigroup (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a) :
    reflectedFellerCurvatureCurve L hL D f (s + a) =
      reflectedFellerTimeOperator L hL D s (reflectedFellerCurvatureCurve L hL D f a) := by
  have hp := (reflectedFellerTimeOperator L hL D s).hasFDerivAt.comp_hasDerivAt a
    (reflectedFellerTimeOperator_hasDerivAt L hL D hD f a ha)
  have hsa : 0 < s + a := add_pos_of_nonneg_of_pos hs ha
  have hd := (reflectedFellerTimeOperator_hasDerivAt L hL D hD f (s + a) hsa).scomp_of_eq a
    ((hasDerivAt_id a).const_add s) (by simp)
  simp only [id_eq, Function.comp_def, one_smul] at hd hp
  have hd' : HasDerivAt (fun r : ℝ => reflectedFellerTimeOperator L hL D s
      (reflectedFellerTimeOperator L hL D r f)) (reflectedFellerDerivativeCurve L hL D f (s + a)) a := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ha] with r hr
    exact (reflectedFellerTimeOperator_add L hL D hD.le f s r hs hr.le).symm
  have he : reflectedFellerDerivativeCurve L hL D f (s + a) =
      reflectedFellerTimeOperator L hL D s (reflectedFellerDerivativeCurve L hL D f a) :=
    hd'.deriv.symm.trans hp.deriv
  rw [reflectedFellerCurvatureCurve, he, reflectedFellerCurvatureCurve, map_smul]

theorem reflectedFeller_positive_time_variation (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    reflectedFellerTimeOperator L hL D b f - reflectedFellerTimeOperator L hL D a f =
      D • ∫ r in a..b, reflectedFellerCurvatureCurve L hL D f r := by
  have hpos (r : ℝ) (hr : r ∈ uIcc a b) : 0 < r :=
    (lt_min ha hb).trans_le hr.1
  have hi : IntervalIntegrable (reflectedFellerDerivativeCurve L hL D f) volume a b :=
    ((reflectedFellerDerivativeCurve_continuousOn L hL D hD f).mono
      (fun r hr => hpos r hr)).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => reflectedFellerTimeOperator_hasDerivAt L hL D hD f r (hpos r hr)) hi
  have hcurve : reflectedFellerDerivativeCurve L hL D f =
      fun r => D • reflectedFellerCurvatureCurve L hL D f r :=
    funext (fun r => (reflectedFellerCurvatureCurve_scaled L hL D hD f r).symm)
  change (∫ r in a..b, reflectedFellerDerivativeCurve L hL D f r) = _ at he
  rw [hcurve, intervalIntegral.integral_smul] at he
  exact he.symm

theorem reflectedFeller_positive_time_semigroup_variation (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f : C(Icc (0 : ℝ) L, ℝ))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    reflectedFellerTimeOperator L hL D b f - reflectedFellerTimeOperator L hL D a f =
      reflectedFellerIntegralOperator L hL D (b - a) (D • reflectedFellerCurvatureCurve L hL D f a) := by
  obtain ⟨F, hf, hcurv⟩ := reflectedFellerCurvatureCurve_representation L hL D hD f a ha
  have he := F.feller_integral hL D hD.le (b - a) (sub_nonneg.mpr hab)
  rw [hf, hcurv] at he
  rw [← reflectedFellerTimeOperator_add L hL D hD.le f (b - a) a
    (sub_nonneg.mpr hab) ha.le, sub_add_cancel] at he
  exact he

end TimeTraps.Probability
