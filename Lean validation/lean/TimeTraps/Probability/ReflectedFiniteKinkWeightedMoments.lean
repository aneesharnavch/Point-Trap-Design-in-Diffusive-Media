module

public import TimeTraps.Probability.ReflectedFiniteKinkWeightedLimit
public import TimeTraps.Probability.ReflectedFiniteKinkC2Moments
public import TimeTraps.Probability.ReflectedAtomicWeightedBoundary
public import TimeTraps.Probability.ReflectedAtomicWeightedCurvature

@[expose] public section

/-! Square integrability of the actual survival-weighted finite-kink
formula. The hazard term is the literal Stieltjes integral, identified
almost surely with its finite weighted contact sum. Signed kink
coefficients, repeated sites and an empty finite family are retained. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

def reflectedFiniteKinkC2WeightedHazard (F : ℝ → ℝ)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  ∫ r in Ioc (0 : ℝ) T.val,
    finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) *
      reflectedAtomicSurvival L D x a κ r.toNNReal ω
      ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω

theorem reflectedFiniteKinkC2_weighted_value_memLp (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    MemLp (fun ω => reflectedAtomicSurvival L D x a κ T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω))
      2 brownianDyadicMeasure := by
  have hv := reflectedFiniteKinkC2_value_memLp hF L hL D x a c T
  have hφ : Measurable (fun ω : ℕ → ℝ => (T, ω)) := measurable_const.prodMk measurable_id
  have hw := (reflectedAtomicSurvival_jointlyMeasurable L D x a κ).comp hφ
  apply hv.of_le_mul (c := (1 : ℝ)) (hw.aestronglyMeasurable.mul hv.aestronglyMeasurable)
  filter_upwards [] with ω
  have hb := reflectedAtomicSurvival_bounds L hD x a κ hκ T ω
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos hb.1]
  exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)

theorem reflectedFiniteKinkC2WeightedHazard_sum_ae
    (F : ℝ → ℝ) (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    reflectedFiniteKinkC2WeightedHazard F L hL D hD a c κ hκ x T =ᵐ[brownianDyadicMeasure]
      (fun ω => ∑ i, κ i * finiteKinkPotential F Finset.univ a c (a i) *
        reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω) := by
  filter_upwards [reflectedAtomicHazardTimeMeasure_weighted_contact_ae L hL D hD x a κ hκ ha,
    reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hc hw
  have he := (hc (fun t => reflectedAtomicSurvival L D x a κ t ω) hw.2.2.2.1
    (finiteKinkPotential F Finset.univ a c) T).2
  calc
    _ = ∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω *
        finiteKinkPotential F Finset.univ a c
          (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)
        ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω :=
      integral_congr_ae (Eventually.of_forall (fun _ => mul_comm _ _))
    _ = _ := he

theorem reflectedFiniteKinkC2WeightedHazard_memLp
    (F : ℝ → ℝ) (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    MemLp (reflectedFiniteKinkC2WeightedHazard F L hL D hD a c κ hκ x T)
      2 brownianDyadicMeasure := by
  have hs : MemLp (fun ω => ∑ i, κ i * finiteKinkPotential F Finset.univ a c (a i) *
      reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω) 2 brownianDyadicMeasure :=
    memLp_finsetSum Finset.univ (fun i _ =>
      (reflectedAtomicWeightedOccupation_memLp L hL D hD x a κ hκ i T).const_mul
        (κ i * finiteKinkPotential F Finset.univ a c (a i)))
  exact hs.ae_eq (reflectedFiniteKinkC2WeightedHazard_sum_ae F L hL D hD a c κ ha hκ x T).symm

theorem reflectedFiniteKinkC2_weighted_occupation_sum_memLp
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    MemLp (fun ω => ∑ i, c i * reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω)
      2 brownianDyadicMeasure :=
  memLp_finsetSum Finset.univ (fun i _ =>
    (reflectedAtomicWeightedOccupation_memLp L hL D hD x a κ hκ i T).const_mul (c i))

theorem reflectedFiniteKinkC2WeightedLimit_eq
    (F : ℝ → ℝ) (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedFiniteKinkC2WeightedLimit F L hL D hD a c κ hκ x T ω =
      D * reflectedAtomicWeightedCurvature F L D x a κ T ω +
      2 * D * (∑ i, c i * reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω) +
      finiteKinkSlope F Finset.univ a c 0 * reflectedAtomicWeightedBoundary L hL D hD x a κ 0 T ω -
      finiteKinkSlope F Finset.univ a c L * reflectedAtomicWeightedBoundary L hL D hD x a κ 1 T ω -
      reflectedFiniteKinkC2WeightedHazard F L hL D hD a c κ hκ x T ω := rfl

theorem reflectedFiniteKinkC2WeightedLimit_memLp (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    MemLp (reflectedFiniteKinkC2WeightedLimit F L hL D hD a c κ hκ x T)
      2 brownianDyadicMeasure := by
  have hd := (reflectedAtomicWeightedCurvature_memLp hF L hL D hD x a κ hκ T).const_mul D
  have hi := (reflectedFiniteKinkC2_weighted_occupation_sum_memLp L hL D hD a c κ hκ x T).const_mul (2 * D)
  have h0 := (reflectedAtomicWeightedBoundary_memLp L hL D hD x a κ hκ 0 T).const_mul
    (finiteKinkSlope F Finset.univ a c 0)
  have h1 := (reflectedAtomicWeightedBoundary_memLp L hL D hD x a κ hκ 1 T).const_mul
    (finiteKinkSlope F Finset.univ a c L)
  have hA := reflectedFiniteKinkC2WeightedHazard_memLp F L hL D hD a c κ ha hκ x T
  exact ((((hd.add hi).add h0).sub h1).sub hA).ae_eq
    (Eventually.of_forall (fun ω =>
      (reflectedFiniteKinkC2WeightedLimit_eq F L hL D hD a c κ hκ x T ω).symm))

end TimeTraps.Probability

end
