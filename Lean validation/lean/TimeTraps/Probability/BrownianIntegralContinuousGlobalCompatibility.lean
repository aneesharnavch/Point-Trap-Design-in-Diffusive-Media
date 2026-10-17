module

public import TimeTraps.Probability.BrownianIntegralContinuousExtensionPath

@[expose] public section

/-! Countably many compact-horizon versions agree on one measurable
full-measure event. Equality on countable dense sets extends to the
entire common time interval by the already proved path continuity. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

def brownianIntegralHorizonPath (T : ℝ≥0) (f : BrownianIntegrand) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  brownianIntegralContinuousPath T f ⟨min t T, zero_le, min_le_right _ _⟩ ω

theorem brownianIntegralHorizonPath_continuous (T : ℝ≥0) (f : BrownianIntegrand) (ω : ℕ → ℝ) :
    Continuous (fun t => brownianIntegralHorizonPath T f t ω) :=
  (brownianIntegralContinuousPath_continuous T f ω).comp
    ((continuous_id.min continuous_const).subtype_mk (fun _ => ⟨zero_le, min_le_right _ _⟩))

theorem brownianIntegralHorizonPath_measurable (T : ℝ≥0) (f : BrownianIntegrand) (t : ℝ≥0) :
    Measurable (brownianIntegralHorizonPath T f t) :=
  (brownianIntegralContinuousPath_stronglyMeasurable T f
    ⟨min t T, zero_le, min_le_right _ _⟩).measurable

theorem brownianIntegralHorizonPath_integral_ae (T : ℝ≥0) (f : BrownianIntegrand)
    (t : ℝ≥0) (ht : t ≤ T) :
    brownianIntegralHorizonPath T f t =ᵐ[brownianDyadicMeasure]
      brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t f := by
  change brownianIntegralContinuousPath T f ⟨min t T, zero_le, min_le_right _ _⟩ =ᵐ[brownianDyadicMeasure] _
  simpa only [min_eq_left ht] using
    brownianIntegralContinuousPath_integral_ae T f ⟨t, zero_le, ht⟩

def brownianIntegralCommonTime (n m k : ℕ) : ℝ≥0 :=
  (denseSeq (BrownianCompactTime (min (n : ℝ≥0) (m : ℝ≥0))) k).val

def brownianIntegralGlobalCompatible (f : BrownianIntegrand) (ω : ℕ → ℝ) : Prop :=
  ∀ n m k : ℕ,
    brownianIntegralHorizonPath n f (brownianIntegralCommonTime n m k) ω =
      brownianIntegralHorizonPath m f (brownianIntegralCommonTime n m k) ω

theorem brownianIntegralGlobalCompatible_measurableSet (f : BrownianIntegrand) :
    MeasurableSet {ω | brownianIntegralGlobalCompatible f ω} := by
  simp only [brownianIntegralGlobalCompatible, ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_eq_fun (brownianIntegralHorizonPath_measurable n f _)
    (brownianIntegralHorizonPath_measurable m f _)

theorem brownianIntegralGlobalCompatible_ae (f : BrownianIntegrand) :
    ∀ᵐ ω ∂brownianDyadicMeasure, brownianIntegralGlobalCompatible f ω := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro k
  have ht := (denseSeq (BrownianCompactTime (min (n : ℝ≥0) (m : ℝ≥0))) k).property.2
  exact (brownianIntegralHorizonPath_integral_ae n f (brownianIntegralCommonTime n m k)
    (ht.trans (min_le_left _ _))).trans
      (brownianIntegralHorizonPath_integral_ae m f (brownianIntegralCommonTime n m k)
        (ht.trans (min_le_right _ _))).symm

theorem brownianIntegralGlobalCompatible_eq {f : BrownianIntegrand} {ω : ℕ → ℝ}
    (hω : brownianIntegralGlobalCompatible f ω) (n m : ℕ) (t : ℝ≥0)
    (hn : t ≤ n) (hm : t ≤ m) :
    brownianIntegralHorizonPath n f t ω = brownianIntegralHorizonPath m f t ω := by
  have he : (fun s : BrownianCompactTime (min (n : ℝ≥0) (m : ℝ≥0)) =>
      brownianIntegralHorizonPath n f s.val ω) =
      (fun s : BrownianCompactTime (min (n : ℝ≥0) (m : ℝ≥0)) =>
        brownianIntegralHorizonPath m f s.val ω) := by
    apply (denseRange_denseSeq (BrownianCompactTime (min (n : ℝ≥0) (m : ℝ≥0)))).equalizer
      ((brownianIntegralHorizonPath_continuous n f ω).comp continuous_subtype_val)
      ((brownianIntegralHorizonPath_continuous m f ω).comp continuous_subtype_val)
    exact funext (hω n m)
  exact congrFun he ⟨t, zero_le, le_min hn hm⟩

end TimeTraps.Probability

end
