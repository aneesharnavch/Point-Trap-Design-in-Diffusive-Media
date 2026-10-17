module

public import TimeTraps.Probability.BrownianAEContinuousMultiplierStep
public import TimeTraps.Probability.BrownianAdaptedContinuousMultiplierDomain

@[expose] public section

/-! Almost-everywhere raw adaptation suffices for multiplication to
preserve the actual closed Brownian integrand domain. Finite dyadic
representatives produce domain elements with the original step
coefficients; the existing product-L² dominated convergence theorem
uses the original almost-sure continuous paths. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B H : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {M : ℝ≥0}

def brownianAEContinuousProductStep (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
    (M : ℝ≥0) (T : ℝ≥0) (n : ℕ)
    (f : brownianIntegralSpace B hBm P) : brownianIntegralSpace B hBm P :=
  @brownianAEPastStepIntegrand Ω mΩ B hBm P (2 ^ n)
    (brownianDyadicGrid T n) (brownianDyadicGrid_monotone T n)
    (fun i => H (brownianDyadicGrid T n i.castSucc))
    (fun i => hH (brownianDyadicGrid T n i.castSucc)) M f

theorem brownianAEContinuousProductStep_coe (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ)
    (f : brownianIntegralSpace B hBm P) :
    ((brownianAEContinuousProductStep hBm hH M T n f : brownianIntegralSpace B hBm P) :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => brownianSquareStepProcess H T n p * (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p) :=
  brownianAEPastStepIntegrand_coe (brownianDyadicGrid T n) (brownianDyadicGrid_monotone T n)
    (fun i => H (brownianDyadicGrid T n i.castSucc))
    (fun i => hH (brownianDyadicGrid T n i.castSucc))
    (fun i => hb (brownianDyadicGrid T n i.castSucc)) f

theorem brownianAEContinuousMultiplier_step_mem_space
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ)
    (e : BrownianIntegralElementary B hBm P) :
    brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuous_step_measurable
        (fun _t => hjoint.comp (measurable_const.prodMk measurable_id)) T n)
      (brownianAdaptedContinuousMultiplier_step_bound hb T n) e.processL2 ∈
      brownianIntegralSpace B hBm P := by
  let S := brownianAEContinuousProductStep hBm hH M T n (brownianIntegralGenerator e)
  have he : brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuous_step_measurable
        (fun t => hjoint.comp (measurable_const.prodMk measurable_id)) T n)
      (brownianAdaptedContinuousMultiplier_step_bound hb T n) e.processL2 =
      (S : Lp ℝ 2 ((volume : Measure ℝ).prod P)) := by
    apply Lp.ext
    exact (brownianAdaptedContinuousMultiplierAmbient_coe _ _ _).trans
      (brownianAEContinuousProductStep_coe hBm hH hb T n (brownianIntegralGenerator e)).symm
  rw [he]
  exact S.property

theorem brownianAEContinuousMultiplier_elementary_mem_space
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
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
        brownianAEContinuousMultiplier_step_mem_space hBm hH hjoint hb e.right n e))
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

theorem brownianAEContinuousMultiplier_mem_space
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
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
    exact brownianAEContinuousMultiplier_elementary_mem_space hB hBm hH hjoint hb hcont e
  have hc : IsClosed ((brownianIntegralSpace B hBm P).comap A.toLinearMap :
      Set (Lp ℝ 2 ((volume : Measure ℝ).prod P))) :=
    (Submodule.isClosed_topologicalClosure (brownianIntegralStepSpace B hBm P)).preimage A.continuous
  exact Submodule.topologicalClosure_minimal _ hs hc hf

end TimeTraps.Probability

end
