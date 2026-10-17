module

public import TimeTraps.Probability.BrownianIntegralElementaryPath
public import TimeTraps.Probability.BrownianIntegralRepresentation
public import TimeTraps.Probability.BrownianJointMeasurability

@[expose] public section

/-! Actual continuous-path representatives for finite elementary sums.
The empty sum is included. The modification statement has the order of
quantifiers “for each time, almost surely”; it does not identify the
chosen conditional-expectation process simultaneously at every real time. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}
variable {I : Type*} [Fintype I]

def brownianElementarySumPath (a : I → BrownianIntegralElementary B hBm P)
    (t : ℝ≥0) (ω : Ω) : ℝ := ∑ i, (a i).integralPath t ω

theorem brownianElementarySumPath_jointly_measurable
    (a : I → BrownianIntegralElementary B hBm P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) :
    Measurable (fun p : ℝ≥0 × Ω => brownianElementarySumPath a p.1 p.2) := by
  apply Finset.measurable_sum
  intro i _
  exact (a i).integralPath_jointly_measurable hjoint

theorem brownianElementarySumPath_stronglyAdapted
    (a : I → BrownianIntegralElementary B hBm P) :
    StronglyAdapted (brownianNaturalFiltration B hBm) (brownianElementarySumPath a) := by
  intro t
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  exact (a i).integralPath_stronglyAdapted t

theorem brownianElementarySumPath_continuous
    (a : I → BrownianIntegralElementary B hBm P) {ω : Ω}
    (hω : Continuous (fun t => B t ω)) :
    Continuous (fun t => brownianElementarySumPath a t ω) := by
  apply continuous_finsetSum
  intro i _
  exact (a i).integralPath_continuous hω

theorem brownianElementarySumPath_integralUpTo_ae (hB : IsPreBrownianReal B P)
    (a : I → BrownianIntegralElementary B hBm P) (t : ℝ≥0) :
    brownianElementarySumPath a t =ᵐ[P] brownianIntegralUpTo hB t (brownianElementarySumIntegrand a) := by
  have he : brownianIntegralUpTo hB t (brownianElementarySumIntegrand a) =
      ∑ i, brownianIntegralUpTo hB t (brownianIntegralGenerator (a i)) := by
    rw [brownianElementarySumIntegrand, map_sum]
  rw [he]
  have hall : ∀ᵐ ω ∂P, ∀ i, (a i).integralPath t ω =
      brownianIntegralUpTo hB t (brownianIntegralGenerator (a i)) ω :=
    ae_all_iff.mpr (fun i => (a i).integralPath_integralUpTo_ae hB t)
  have hsum : brownianElementarySumPath a t =ᵐ[P]
      (fun ω => ∑ i, brownianIntegralUpTo hB t (brownianIntegralGenerator (a i)) ω) := by
    filter_upwards [hall] with ω hω
    exact Finset.sum_congr rfl (fun i _ => hω i)
  exact hsum.trans (Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => brownianIntegralUpTo hB t (brownianIntegralGenerator (a i)))).symm

theorem brownianElementarySumPath_martingale_ae (hB : IsPreBrownianReal B P)
    (a : I → BrownianIntegralElementary B hBm P) (t : ℝ≥0) :
    brownianElementarySumPath a t =ᵐ[P] brownianIntegralProcess hB (brownianElementarySumIntegrand a) t :=
  (brownianElementarySumPath_integralUpTo_ae hB a t).trans
    (brownianIntegralProcess_ae hB (brownianElementarySumIntegrand a) t).symm

theorem brownianElementarySumPath_martingale (hB : IsPreBrownianReal B P)
    (a : I → BrownianIntegralElementary B hBm P) :
    Martingale (brownianElementarySumPath a) (brownianNaturalFiltration B hBm) P :=
  (brownianIntegralProcess_martingale hB (brownianElementarySumIntegrand a)).congr
    (brownianElementarySumPath_stronglyAdapted a)
    (fun t => (brownianElementarySumPath_martingale_ae hB a t).symm)

theorem brownianElementarySumPath_continuous_ae (hB : IsBrownianReal B P)
    (a : I → BrownianIntegralElementary B hBm P) :
    ∀ᵐ ω ∂P, Continuous (fun t => brownianElementarySumPath a t ω) :=
  hB.cont.mono (fun _ hω => brownianElementarySumPath_continuous a hω)

theorem brownianDyadicElementarySumPath_continuous_modification
    (a : I → BrownianIntegralElementary brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure) :
    (∀ t, brownianElementarySumPath a t =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegralProcess (brownianElementarySumIntegrand a) t) ∧
      (∀ᵐ ω ∂brownianDyadicMeasure, Continuous (fun t => brownianElementarySumPath a t ω)) :=
  ⟨fun t => brownianElementarySumPath_martingale_ae brownianDyadicPath_isPreBrownianReal a t,
    brownianElementarySumPath_continuous_ae brownianDyadicPath_isBrownianReal a⟩

theorem brownianDyadicElementarySumPath_jointly_measurable
    (a : I → BrownianIntegralElementary brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianElementarySumPath a p.1 p.2) :=
  brownianElementarySumPath_jointly_measurable a brownianDyadicPath_jointly_measurable

end TimeTraps.Probability
