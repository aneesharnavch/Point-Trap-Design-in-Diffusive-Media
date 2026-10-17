module

public import TimeTraps.Probability.BrownianWeightedQuadraticDyadic

@[expose] public section

/-! Bounded measurable functions of the Brownian left endpoint supply
actual signed adapted weights. Their compensated quadratic sums converge
to zero in L², including for the constructed Brownian process. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ}

noncomputable def brownianWeightedDyadicFunction (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (n : ℕ) : Ω → ℝ :=
  brownianWeightedDyadicQuadratic B T n (fun i ω => g (B (brownianDyadicGrid T n i.castSucc) ω))

theorem brownianWeightedFunction_adapted (hBm : ∀ t, Measurable (B t)) (hg : Measurable g)
    (T : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) :
    StronglyMeasurable[brownianNaturalFiltration B hBm (brownianDyadicGrid T n i.castSucc)]
      (fun ω => g (B (brownianDyadicGrid T n i.castSucc) ω)) :=
  (hg.comp (brownianNaturalFiltration_stronglyAdapted B hBm _).measurable).stronglyMeasurable

theorem brownianWeightedDyadicFunction_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : Measurable g) (M : ℝ≥0) (hb : ∀ x, |g x| ≤ M.val)
    (T : ℝ≥0) (n : ℕ) : (∫ ω, brownianWeightedDyadicFunction B g T n ω ∂P) = 0 :=
  brownianWeightedDyadicQuadratic_mean hB hBm T n _ (brownianWeightedFunction_adapted hBm hg T n) M
    (fun _ => Eventually.of_forall (fun _ => hb _))

theorem brownianWeightedDyadicFunction_secondMoment_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : Measurable g) (M : ℝ≥0) (hb : ∀ x, |g x| ≤ M.val)
    (T : ℝ≥0) (n : ℕ) :
    (∫ ω, brownianWeightedDyadicFunction B g T n ω ^ 2 ∂P) ≤
      2 * M.val ^ 2 * T.val ^ 2 / (2 : ℝ) ^ n :=
  brownianWeightedDyadicQuadratic_secondMoment_le hB hBm T n _
    (brownianWeightedFunction_adapted hBm hg T n) M (fun _ => Eventually.of_forall (fun _ => hb _))

theorem brownianWeightedDyadicFunction_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : Measurable g) (M : ℝ≥0) (hb : ∀ x, |g x| ≤ M.val)
    (T : ℝ≥0) (n : ℕ) : MemLp (brownianWeightedDyadicFunction B g T n) 2 P :=
  brownianWeightedDyadicQuadratic_memLp hB hBm T n _ (brownianWeightedFunction_adapted hBm hg T n) M
    (fun _ => Eventually.of_forall (fun _ => hb _))

noncomputable def brownianWeightedDyadicFunctionL2 (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (n : ℕ) (hSum : MemLp (brownianWeightedDyadicFunction B g T n) 2 P) : Lp ℝ 2 P :=
  brownianWeightedDyadicQuadraticL2 B T n _ hSum

theorem brownianWeightedDyadicFunctionL2_coe (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (n : ℕ) (hSum : MemLp (brownianWeightedDyadicFunction B g T n) 2 P) :
    brownianWeightedDyadicFunctionL2 B g T n hSum =ᵐ[P] brownianWeightedDyadicFunction B g T n :=
  brownianWeightedDyadicQuadraticL2_coe B T n _ hSum

theorem brownianWeightedDyadicFunctionL2_norm_sq_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : Measurable g) (M : ℝ≥0) (hb : ∀ x, |g x| ≤ M.val)
    (T : ℝ≥0) (n : ℕ) (hSum : MemLp (brownianWeightedDyadicFunction B g T n) 2 P) :
    ‖brownianWeightedDyadicFunctionL2 B g T n hSum‖ ^ 2 ≤
      2 * M.val ^ 2 * T.val ^ 2 / (2 : ℝ) ^ n :=
  brownianWeightedDyadicQuadraticL2_norm_sq_le hB hBm T n _ (brownianWeightedFunction_adapted hBm hg T n) M
    (fun _ => Eventually.of_forall (fun _ => hb _)) hSum

theorem brownianWeightedDyadicFunctionL2_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : Measurable g) (M : ℝ≥0) (hb : ∀ x, |g x| ≤ M.val) (T : ℝ≥0) :
    Tendsto (fun n => brownianWeightedDyadicFunctionL2 B g T n
      (brownianWeightedDyadicFunction_memLp hB hBm hg M hb T n))
      atTop (𝓝 (0 : Lp ℝ 2 P)) :=
  brownianWeightedDyadicQuadraticL2_tendsto hB hBm T _
    (fun n => brownianWeightedFunction_adapted hBm hg T n) M
    (fun _ _ => Eventually.of_forall (fun _ => hb _))
    (brownianWeightedDyadicFunction_memLp hB hBm hg M hb T)

theorem brownianDyadicPath_weightedQuadratic_converges (hg : Measurable g)
    (M : ℝ≥0) (hb : ∀ x, |g x| ≤ M.val) (T : ℝ≥0) :
    Tendsto (fun n => brownianWeightedDyadicFunctionL2 brownianDyadicPath g T n
      (brownianWeightedDyadicFunction_memLp brownianDyadicPath_isPreBrownianReal
        brownianDyadicPath_measurable hg M hb T n))
      atTop (𝓝 (0 : Lp ℝ 2 brownianDyadicMeasure)) :=
  brownianWeightedDyadicFunctionL2_tendsto brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable hg M hb T

end TimeTraps.Probability
