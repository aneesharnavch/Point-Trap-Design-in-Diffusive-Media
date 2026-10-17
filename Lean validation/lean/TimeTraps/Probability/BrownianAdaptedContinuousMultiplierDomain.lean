module

public import TimeTraps.Probability.BrownianAdaptedContinuousMultiplierElementary
public import TimeTraps.Probability.BrownianAdaptedContinuousMultiplierConvergence

@[expose] public section

/-! Multiplication preserves the actual closed Brownian integrand domain.
For an elementary input, bounded left dyadic samples of the multiplier
give finite elementary products. Their weighted product-L² limit is the
desired product. Continuity then extends this fact from the elementary
span to its closure, without a predictable-space density premise. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B H : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {M : ℝ≥0}

theorem brownianAdaptedContinuousMultiplier_raw_measurable
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2)) :
    Measurable (fun p : ℝ × Ω => H p.1.toNNReal p.2) :=
  hjoint.comp ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd)

theorem brownianAdaptedContinuousMultiplier_step_bound
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) :
    |brownianSquareStepProcess H T n p| ≤ M.val := by
  have h := brownianAdaptedContinuous_step_bound hb T n p
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · have hi : brownianIntervalIndicator 0 T p.1 = 1 := Set.indicator_of_mem hp _
    simpa only [hi, mul_one] using h
  · have hi : brownianIntervalIndicator 0 T p.1 = 0 := Set.indicator_of_notMem hp _
    rw [hi, mul_zero] at h
    exact h.trans M.property

theorem brownianAdaptedContinuousMultiplier_cutoff_bound
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (p : ℝ × Ω) :
    |brownianSquareProcess H T p| ≤ M.val := by
  have h := brownianAdaptedContinuous_cutoff_bound hb T p
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · have hi : brownianIntervalIndicator 0 T p.1 = 1 := Set.indicator_of_mem hp _
    simpa only [hi, mul_one] using h
  · have hi : brownianIntervalIndicator 0 T p.1 = 0 := Set.indicator_of_notMem hp _
    rw [hi, mul_zero] at h
    exact h.trans M.property

theorem brownianAdaptedContinuousMultiplier_step_mem_space
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ)
    (e : BrownianIntegralElementary B hBm P) :
    brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuous_step_measurable
        (fun _t => hjoint.comp (measurable_const.prodMk measurable_id)) T n)
      (brownianAdaptedContinuousMultiplier_step_bound hb T n) e.processL2 ∈
      brownianIntegralSpace B hBm P := by
  let a := brownianAdaptedContinuousElementary hB hBm hH hb T n
  let c := fun i : Fin (2 ^ n) => (a i).boundedProduct e (hb (brownianDyadicGrid T n i.castSucc))
  have he : brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuous_step_measurable
        (fun t => hjoint.comp (measurable_const.prodMk measurable_id)) T n)
      (brownianAdaptedContinuousMultiplier_step_bound hb T n) e.processL2 =
      (brownianElementarySumIntegrand c : Lp ℝ 2 ((volume : Measure ℝ).prod P)) := by
    apply Lp.ext
    filter_upwards [brownianAdaptedContinuousMultiplierAmbient_coe
      (brownianAdaptedContinuous_step_measurable
        (fun t => hjoint.comp (measurable_const.prodMk measurable_id)) T n)
      (brownianAdaptedContinuousMultiplier_step_bound hb T n) e.processL2,
      e.processL2_coe, brownianElementarySumIntegrand_coe c] with p hm he hc
    rw [hm, he, hc]
    change (∑ i, brownianElementaryProcess (a i).left (a i).right (a i).coefficient p) *
      brownianElementaryProcess e.left e.right e.coefficient p =
      ∑ i, brownianElementaryProcess (c i).left (c i).right (c i).coefficient p
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact (brownianAdaptedContinuousMultiplier_elementary_process (a i) e
      (hb (brownianDyadicGrid T n i.castSucc)) p).symm
  rw [he]
  exact (brownianElementarySumIntegrand c).property

theorem brownianAdaptedContinuousMultiplier_elementary_mem_space
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (e : BrownianIntegralElementary B hBm P) :
    brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuousMultiplier_raw_measurable hjoint)
      (fun p => hb p.1.toNNReal p.2) e.processL2 ∈ brownianIntegralSpace B hBm P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hlim := brownianAdaptedContinuousMultiplier_tendsto
    (brownianSquareProcess_measurable hjoint e.right)
    (fun n => brownianAdaptedContinuous_step_measurable
      (fun t => hjoint.comp (measurable_const.prodMk measurable_id)) e.right n)
    (brownianAdaptedContinuousMultiplier_cutoff_bound hb e.right)
    (brownianAdaptedContinuousMultiplier_step_bound hb e.right)
    (brownianAdaptedContinuous_step_tendsto_ae hcont e.right) e.processL2
  have hcut : brownianAdaptedContinuousMultiplierAmbient
      (brownianSquareProcess_measurable hjoint e.right)
      (brownianAdaptedContinuousMultiplier_cutoff_bound hb e.right) e.processL2 ∈
      brownianIntegralSpace B hBm P :=
    (Submodule.isClosed_topologicalClosure (brownianIntegralStepSpace B hBm P)).mem_of_tendsto
      hlim (Eventually.of_forall (fun n =>
        brownianAdaptedContinuousMultiplier_step_mem_space hB hBm hH hjoint hb e.right n e))
  have he : brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuousMultiplier_raw_measurable hjoint)
      (fun p => hb p.1.toNNReal p.2) e.processL2 =
      brownianAdaptedContinuousMultiplierAmbient
        (brownianSquareProcess_measurable hjoint e.right)
        (brownianAdaptedContinuousMultiplier_cutoff_bound hb e.right) e.processL2 := by
    apply Lp.ext
    filter_upwards [brownianAdaptedContinuousMultiplierAmbient_coe
      (brownianAdaptedContinuousMultiplier_raw_measurable hjoint)
      (fun p => hb p.1.toNNReal p.2) e.processL2,
      brownianAdaptedContinuousMultiplierAmbient_coe
        (brownianSquareProcess_measurable hjoint e.right)
        (brownianAdaptedContinuousMultiplier_cutoff_bound hb e.right) e.processL2,
      e.processL2_coe] with p hr hc he
    rw [hr, hc, he]
    by_cases hp : p.1 ∈ Ioc e.left.val e.right.val
    · have hpT : p.1 ∈ Ioc (0 : ℝ) e.right.val :=
        ⟨lt_of_le_of_lt e.left.property hp.1, hp.2⟩
      change H p.1.toNNReal p.2 * _ =
        ((Ioc (0 : ℝ) e.right.val).indicator (fun _ => 1) p.1 * H p.1.toNNReal p.2) * _
      rw [Set.indicator_of_mem hpT, one_mul]
    · have hz : brownianElementaryProcess e.left e.right e.coefficient p = 0 := by
        change (Ioc e.left.val e.right.val).indicator (fun _ => 1) p.1 * e.coefficient p.2 = 0
        rw [Set.indicator_of_notMem hp, zero_mul]
      rw [hz, mul_zero, mul_zero]
  rw [he]
  exact hcut

theorem brownianAdaptedContinuousMultiplier_mem_space
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {f : Lp ℝ 2 ((volume : Measure ℝ).prod P)} (hf : f ∈ brownianIntegralSpace B hBm P) :
    brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuousMultiplier_raw_measurable hjoint)
      (fun p => hb p.1.toNNReal p.2) f ∈ brownianIntegralSpace B hBm P := by
  let A := brownianAdaptedContinuousMultiplierAmbient (P := P)
    (brownianAdaptedContinuousMultiplier_raw_measurable hjoint) (fun p => hb p.1.toNNReal p.2)
  have hs : brownianIntegralStepSpace B hBm P ≤
      (brownianIntegralSpace B hBm P).comap A.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact brownianAdaptedContinuousMultiplier_elementary_mem_space hB hBm hH hjoint hb hcont e
  have hc : IsClosed ((brownianIntegralSpace B hBm P).comap A.toLinearMap :
      Set (Lp ℝ 2 ((volume : Measure ℝ).prod P))) :=
    (Submodule.isClosed_topologicalClosure (brownianIntegralStepSpace B hBm P)).preimage A.continuous
  exact Submodule.topologicalClosure_minimal _ hs hc hf

end TimeTraps.Probability

end
