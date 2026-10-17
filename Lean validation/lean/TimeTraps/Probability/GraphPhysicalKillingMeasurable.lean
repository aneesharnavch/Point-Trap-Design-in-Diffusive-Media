module

public import TimeTraps.Probability.GraphPhysicalKillingSpeedData

@[expose] public section

/-! Almost-everywhere measurability of the literal WithTop real physical
attainment time itself, retaining infinity and the original definition. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

theorem GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetime_aemeasurable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x : GraphRealization P.geometry)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    AEMeasurable (P.physicalAtomicAttainmentLifetime b hb a κ)
      (exponentialKillingMeasure (P.continuousPathLaw h0 x)) := by
  have hn : NullMeasurable (P.physicalAtomicAttainmentLifetime b hb a κ)
      (exponentialKillingMeasure (P.continuousPathLaw h0 x)) := by
    change @Measurable
      (NullMeasurableSpace (GraphContinuousPath P.geometry × ℝ)
        (exponentialKillingMeasure (P.continuousPathLaw h0 x))) (WithTop ℝ) _ _ _
    apply measurable_of_Ioi
    intro q
    change NullMeasurableSet ((P.physicalAtomicAttainmentLifetime b hb a κ) ⁻¹' Ioi q)
      (exponentialKillingMeasure (P.continuousPathLaw h0 x))
    induction q using WithTop.recTopCoe with
    | top =>
      simpa only [Ioi_top, preimage_empty] using
        (nullMeasurableSet_empty : NullMeasurableSet (∅ : Set (GraphContinuousPath P.geometry × ℝ))
          (exponentialKillingMeasure (P.continuousPathLaw h0 x)))
    | coe r =>
      by_cases hr : 0 ≤ r
      · have he : (P.physicalAtomicAttainmentLifetime b hb a κ) ⁻¹' Ioi (r : WithTop ℝ) =
            {p | ENNReal.ofReal r < P.physicalAtomicAttainmentLifetimeValue b hb a κ p} := by
          ext p
          exact (nonnegativeLifetimeValue_lt_iff r hr _).symm
        rw [he]
        exact nullMeasurableSet_lt aemeasurable_const
          (P.physicalAtomicAttainmentLifetimeValue_aemeasurable h0 b hb x a κ hκ)
      · have he : (P.physicalAtomicAttainmentLifetime b hb a κ) ⁻¹' Ioi (r : WithTop ℝ) = univ := by
          apply eq_univ_of_forall
          intro p
          exact (WithTop.coe_lt_coe.mpr (lt_of_not_ge hr)).trans_le
            (P.physicalAtomicAttainmentLifetime_nonneg b hb a κ p)
        rw [he]
        exact nullMeasurableSet_univ
  exact hn.aemeasurable

end TimeTraps.Analysis
