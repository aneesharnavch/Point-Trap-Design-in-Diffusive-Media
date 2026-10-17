module

public import TimeTraps.Probability.ReflectedInteriorOccupationStieltjes
public import TimeTraps.Probability.StieltjesBoundaryIntegral

@[expose] public section

/-! The actual normalized interior time measure integrates a spatial
weight as its value at the supported level times the actual occupation
coefficient. No regularity of the weight is needed: it is almost surely
constant under this supported time measure. The event is fixed per level,
and on it all finite horizons and all real weights are covered. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedInteriorOccupationTimeMeasure_mass {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : reflectedInteriorLocalTimeRegular x σ L a ω)
    (T : ℝ≥0) :
    reflectedInteriorOccupationTimeMeasure x hσ hL a ω (Ioc (0 : ℝ) T.val) =
      ENNReal.ofReal (reflectedInteriorOccupationCoefficient x σ L a T ω) := by
  rw [reflectedInteriorOccupationTimeMeasure_eq_stieltjes, StieltjesFunction.measure_Ioc,
    reflectedInteriorOccupationStieltjes_apply_nnreal hσ hL hω T,
    reflectedInteriorOccupationStieltjes_zero hσ hL hω, sub_zero]

theorem reflectedInteriorOccupationTimeMeasure_weight_ae {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (ha : a ∈ Ioo 0 L)
    (hω : reflectedInteriorLocalTimeRegular x σ L a ω) (g : ℝ → ℝ) :
    (fun r => g (reflectedFold L (affineBrownianInput x σ r.toNNReal ω)))
      =ᵐ[reflectedInteriorOccupationTimeMeasure x hσ hL a ω] (fun _ => g a) := by
  filter_upwards [(reflectedInteriorOccupationTimeMeasure x hσ hL a ω).support_mem_ae] with r hr
  rw [(reflectedInteriorOccupationTimeMeasure_support hσ hL ha hω hr).2]

theorem reflectedInteriorOccupationTimeMeasure_weight_integrable {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (ha : a ∈ Ioo 0 L)
    (hω : reflectedInteriorLocalTimeRegular x σ L a ω) (g : ℝ → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun r => g (reflectedFold L (affineBrownianInput x σ r.toNNReal ω)))
      (Ioc (0 : ℝ) T.val) (reflectedInteriorOccupationTimeMeasure x hσ hL a ω) := by
  have : IsFiniteMeasure ((reflectedInteriorOccupationTimeMeasure x hσ hL a ω).restrict (Ioc (0 : ℝ) T.val)) :=
    ⟨by rw [Measure.restrict_apply_univ, reflectedInteriorOccupationTimeMeasure_mass hσ hL hω T]
        exact ENNReal.ofReal_lt_top⟩
  have he : (fun r => g (reflectedFold L (affineBrownianInput x σ r.toNNReal ω)))
      =ᵐ[(reflectedInteriorOccupationTimeMeasure x hσ hL a ω).restrict (Ioc (0 : ℝ) T.val)]
        (fun _ => g a) :=
    ae_restrict_of_ae (reflectedInteriorOccupationTimeMeasure_weight_ae hσ hL ha hω g)
  exact (integrable_const (g a)).congr he.symm

theorem reflectedInteriorOccupationTimeMeasure_weight_integral {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (ha : a ∈ Ioo 0 L)
    (hω : reflectedInteriorLocalTimeRegular x σ L a ω) (g : ℝ → ℝ) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val, g (reflectedFold L (affineBrownianInput x σ r.toNNReal ω))
      ∂reflectedInteriorOccupationTimeMeasure x hσ hL a ω) =
      g a * reflectedInteriorOccupationCoefficient x σ L a T ω := by
  have hs : (reflectedInteriorOccupationStieltjes x hσ hL a ω).measure.support ⊆
      {r : ℝ | reflectedFold L (affineBrownianInput x σ r.toNNReal ω) = a} := by
    rw [← reflectedInteriorOccupationTimeMeasure_eq_stieltjes]
    exact fun r hr => (reflectedInteriorOccupationTimeMeasure_support hσ hL ha hω hr).2
  have he := stieltjes_integral_of_supported_level (reflectedInteriorOccupationStieltjes x hσ hL a ω)
    (fun r => reflectedFold L (affineBrownianInput x σ r.toNNReal ω)) a hs g T
  rw [← reflectedInteriorOccupationTimeMeasure_eq_stieltjes,
    reflectedInteriorOccupationStieltjes_apply_nnreal hσ hL hω T,
    reflectedInteriorOccupationStieltjes_zero hσ hL hω, sub_zero] at he
  exact he

theorem reflectedInteriorOccupationTimeMeasure_weight_integral_ae (x : ℝ) {σ L a : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (ha : a ∈ Ioo 0 L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ g : ℝ → ℝ, ∀ T : ℝ≥0,
      IntegrableOn (fun r => g (reflectedFold L (affineBrownianInput x σ r.toNNReal ω)))
        (Ioc (0 : ℝ) T.val) (reflectedInteriorOccupationTimeMeasure x hσ hL a ω) ∧
      (∫ r in Ioc (0 : ℝ) T.val, g (reflectedFold L (affineBrownianInput x σ r.toNNReal ω))
        ∂reflectedInteriorOccupationTimeMeasure x hσ hL a ω) =
        g a * reflectedInteriorOccupationCoefficient x σ L a T ω := by
  filter_upwards [reflectedInteriorLocalTimeRegular_ae x σ L a] with ω hω
  exact fun g T => ⟨reflectedInteriorOccupationTimeMeasure_weight_integrable hσ hL ha hω g T,
    reflectedInteriorOccupationTimeMeasure_weight_integral hσ hL ha hω g T⟩

end TimeTraps.Probability
