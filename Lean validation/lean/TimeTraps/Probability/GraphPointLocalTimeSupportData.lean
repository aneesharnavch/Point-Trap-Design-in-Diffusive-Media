module

public import TimeTraps.Probability.GraphPointLocalTimePath

@[expose] public section

/-! Vanishing of literal graph occupation increments on time intervals
separated from the contact site. Only the actual shrinking bump support
is used, with the original ordinary-length normalization unchanged. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*}

theorem graphOccupation_eq_of_vanishes (G : MetricGraph V E) (f : C(GraphRealization G, ℝ))
    (p : GraphContinuousPath G) (s t : ℝ≥0) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, f (p r) = 0) : graphOccupation G f t p = graphOccupation G f s p := by
  have hc : Continuous (fun r : ℝ => f (p r.toNNReal)) :=
    f.continuous.comp (p.continuous.comp continuous_real_toNNReal)
  have hz : (∫ r in s.val..t.val, f (p r.toNNReal)) = 0 := by
    calc
      _ = ∫ _r in s.val..t.val, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' := uIcc_of_le (show s.val ≤ t.val from hst) ▸ hr
        have hrs : s ≤ r.toNNReal := by
          apply NNReal.coe_le_coe.mp
          rw [Real.coe_toNNReal r (s.property.trans hr'.1)]
          exact hr'.1
        exact hp r.toNNReal ⟨hrs, Real.toNNReal_le_iff_le_coe.mpr hr'.2⟩
      _ = 0 := by simp
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 s.val) (hc.intervalIntegrable s.val t.val)
  rw [hz, add_zero] at hi
  exact hi.symm

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_eq_of_separated
    [Fintype V] [Fintype E] [Nonempty E]
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (n : ℕ)
    (p : GraphContinuousPath P.geometry) (s t : ℝ≥0) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, P.localTimeRadius n ≤ dist (p r) a) :
    P.localTimeApproximant a n p t = P.localTimeApproximant a n p s := by
  apply graphOccupation_eq_of_vanishes P.geometry (P.geometry.pointBump a (P.localTimeRadius n)) p s t hst
  intro r hr
  by_contra hn
  have hb := P.geometry.pointBump_support_subset a (P.localTimeRadius_pos n) hn
  exact (not_lt.mpr (hp r hr)) hb

end TimeTraps.Analysis
