module

public import TimeTraps.Probability.ReflectedAtomicHazardStieltjesIntegral
public import TimeTraps.Probability.ReflectedInteriorOccupationMean
public import TimeTraps.Probability.ReflectedFellerOperator

@[expose] public section

/-! The actual continuous-test integral against one interior occupation
measure. Supported contact gives its value and square integrability;
the established Gaussian local-time mean then gives its expectation.
The level and starting point are fixed before every AE assertion. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

def reflectedAtomicRevuzContact (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x a : ℝ) (g : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  ∫ r in Ioc (0 : ℝ) T.val,
    reflectedFellerExtension L hL g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)
      ∂reflectedInteriorOccupationTimeMeasure x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL a ω

theorem reflectedAtomicRevuzContact_eq_ae (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x a : ℝ) (ha : a ∈ Ioo 0 L) (g : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    reflectedAtomicRevuzContact L hL D hD x a g T =ᵐ[brownianDyadicMeasure]
      fun ω => g ⟨a, Ioo_subset_Icc_self ha⟩ *
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T ω := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  filter_upwards [reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L a] with ω hω
  have he := (reflectedInteriorOccupationTimeMeasure_weighted_contact hσ hL ha hω
    (fun _ => 1) continuous_const (reflectedFellerExtension L hL g) T).2
  have hm := reflectedInteriorOccupationTimeMeasure_mass hσ hL hω T
  have hg : reflectedFellerExtension L hL g a = g ⟨a, Ioo_subset_Icc_self ha⟩ :=
    reflectedFellerExtension_on_interval L hL g ⟨a, Ioo_subset_Icc_self ha⟩
  simp only [one_mul] at he
  change reflectedAtomicRevuzContact L hL D hD x a g T ω = _
  calc
    _ = reflectedFellerExtension L hL g a * ∫ _r in Ioc (0 : ℝ) T.val, (1 : ℝ)
        ∂reflectedInteriorOccupationTimeMeasure x hσ hL a ω := he
    _ = _ := by
      rw [hg]
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ, hm, smul_eq_mul,
        mul_one, ENNReal.toReal_ofReal
          (reflectedInteriorOccupationCoefficient_nonneg x hσ L a T ω)]

theorem reflectedAtomicRevuzContact_memLp (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x a : ℝ) (ha : a ∈ Ioo 0 L) (g : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    MemLp (reflectedAtomicRevuzContact L hL D hD x a g T) 2 brownianDyadicMeasure :=
  ((reflectedInteriorOccupationCoefficient_memLp L hL D hD x a T).const_mul
    (g ⟨a, Ioo_subset_Icc_self ha⟩)).ae_eq (reflectedAtomicRevuzContact_eq_ae L hL D hD x a ha g T).symm

theorem reflectedAtomicRevuzContact_mean (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x a : ℝ) (ha : a ∈ Ioo 0 L) (g : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    (∫ ω, reflectedAtomicRevuzContact L hL D hD x a g T ω ∂brownianDyadicMeasure) =
      g ⟨a, Ioo_subset_Icc_self ha⟩ *
        ∫ r in (0 : ℝ)..T.val, reflectedGaussianDensity L x (2 * D * r).toNNReal a := by
  rw [integral_congr_ae (reflectedAtomicRevuzContact_eq_ae L hL D hD x a ha g T),
    integral_const_mul, reflectedInteriorOccupationCoefficient_gaussian_mean L hL D hD x a T]

end TimeTraps.Probability

end
