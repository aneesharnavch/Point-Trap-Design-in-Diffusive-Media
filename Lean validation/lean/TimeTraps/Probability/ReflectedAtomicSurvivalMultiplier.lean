module

public import TimeTraps.Probability.BrownianAEContinuousMultiplierApproximation
public import TimeTraps.Probability.ReflectedAtomicHazardPaths
public import TimeTraps.Probability.ReflectedAtomicHazardAdapted
public import TimeTraps.Probability.BrownianIntegralContinuousGlobal

@[expose] public section

/-! The actual atomic survival weight acts contractively on the original
Brownian integrand domain. Its left dyadic sums against the continuous
driver version converge to the canonical product integral. The sites
need not be distinct and the finite label type may be empty; identifying
the coefficient with an interior occupation density is a separate fact. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

def reflectedAtomicSurvivalMultiplier (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) : BrownianIntegrand →L[ℝ] BrownianIntegrand :=
  brownianAEContinuousMultiplier (M := 1) brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable (reflectedAtomicSurvival_raw_aestronglyMeasurable L D x a κ)
    (reflectedAtomicSurvival_jointlyMeasurable L D x a κ)
    (fun t ω => by
      rw [abs_of_pos (reflectedAtomicSurvival_bounds L hD x a κ hκ t ω).1]
      exact (reflectedAtomicSurvival_bounds L hD x a κ hκ t ω).2)
    ((reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ).mono (fun _ hω => hω.2.2.2.1))

theorem reflectedAtomicSurvivalMultiplier_coe (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (f : BrownianIntegrand) :
    (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ f :
      Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) =ᵐ[volume.prod brownianDyadicMeasure]
      (fun p => reflectedAtomicSurvival L D x a κ p.1.toNNReal p.2 *
        (f : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) p) := by
  unfold reflectedAtomicSurvivalMultiplier
  exact brownianAEContinuousMultiplier_coe _ _ _ _ _ _ f

theorem reflectedAtomicSurvivalMultiplier_norm (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (f : BrownianIntegrand) :
    ‖reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ f‖ ≤ ‖f‖ := by
  unfold reflectedAtomicSurvivalMultiplier
  exact (brownianAEContinuousMultiplier_norm (M := 1) brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable (reflectedAtomicSurvival_raw_aestronglyMeasurable L D x a κ)
      (reflectedAtomicSurvival_jointlyMeasurable L D x a κ)
      (fun t ω => by
        rw [abs_of_pos (reflectedAtomicSurvival_bounds L hD x a κ hκ t ω).1]
        exact (reflectedAtomicSurvival_bounds L hD x a κ hκ t ω).2)
      ((reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ).mono (fun _ hω => hω.2.2.2.1)) f).trans_eq
        (show ((1 : ℝ≥0) : ℝ) * ‖f‖ = ‖f‖ from one_mul _)

theorem reflectedAtomicSurvivalMultiplier_cutoff (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ≥0) (f : BrownianIntegrand) :
    reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ
      (brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure t f) =
      brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure t
        (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ f) := by
  unfold reflectedAtomicSurvivalMultiplier
  exact brownianAEContinuousMultiplier_cutoff _ _ _ _ _ _ t f

def reflectedAtomicSurvivalProductStep (L D x : ℝ) (a κ : ι → ℝ) (T : ℝ≥0) (n : ℕ)
    (f : BrownianIntegrand) : BrownianIntegrand :=
  brownianAEContinuousProductStep brownianDyadicPath_measurable
    (reflectedAtomicSurvival_raw_aestronglyMeasurable L D x a κ) 1 T n f

theorem reflectedAtomicSurvivalProductStep_integral_ae (L : ℝ) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) (n : ℕ) (f : BrownianIntegrand) :
    brownianIntegral brownianDyadicPath_isPreBrownianReal
      (reflectedAtomicSurvivalProductStep L D x a κ T n f) =ᵐ[brownianDyadicMeasure]
      brownianStepIntegral (brownianIntegralGlobalPath f) (brownianDyadicGrid T n)
        (fun i => reflectedAtomicSurvival L D x a κ (brownianDyadicGrid T n i.castSucc)) := by
  have he := brownianAEContinuousProductStep_integral_ae (M := 1)
    brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    (reflectedAtomicSurvival_raw_aestronglyMeasurable L D x a κ)
    (fun t ω => by
      rw [abs_of_pos (reflectedAtomicSurvival_bounds L hD x a κ hκ t ω).1]
      exact (reflectedAtomicSurvival_bounds L hD x a κ hκ t ω).2) T n f
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ j : Fin (2 ^ n + 1),
      brownianIntegralGlobalPath f (brownianDyadicGrid T n j) ω =
        brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal (brownianDyadicGrid T n j) f ω :=
    ae_all_iff.mpr (fun j => brownianIntegralGlobalPath_integral_ae f (brownianDyadicGrid T n j))
  filter_upwards [he, hall] with ω hω hg
  refine hω.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  change reflectedAtomicSurvival L D x a κ (brownianDyadicGrid T n i.castSucc) ω * _ =
    reflectedAtomicSurvival L D x a κ (brownianDyadicGrid T n i.castSucc) ω * _
  rw [hg i.succ, hg i.castSucc]

theorem reflectedAtomicSurvivalProductStepIntegral_tendsto
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) (f : BrownianIntegrand)
    (hf : brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure T f = f) :
    Tendsto (fun n => brownianIntegral brownianDyadicPath_isPreBrownianReal
      (reflectedAtomicSurvivalProductStep L D x a κ T n f)) atTop
      (𝓝 (brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ f))) :=
  brownianAEContinuousProductStepIntegral_tendsto (M := 1)
    brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    (reflectedAtomicSurvival_raw_aestronglyMeasurable L D x a κ)
    (reflectedAtomicSurvival_jointlyMeasurable L D x a κ)
    (fun t ω => by
      rw [abs_of_pos (reflectedAtomicSurvival_bounds L hD x a κ hκ t ω).1]
      exact (reflectedAtomicSurvival_bounds L hD x a κ hκ t ω).2)
    ((reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ).mono (fun _ hω => hω.2.2.2.1)) T f hf

end TimeTraps.Probability

end
