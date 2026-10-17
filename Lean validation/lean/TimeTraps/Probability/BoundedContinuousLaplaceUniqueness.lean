module

public import TimeTraps.Probability.BoundedContinuousLaplaceDensity

@[expose] public section

/-! Positive Laplace transforms determine bounded continuous functions
at every nonnegative time, including zero. The proof uses finite discounted
measures, the proved exponential-algebra uniqueness, and continuity. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction

theorem nonnegative_boundedContinuous_laplace_unique {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ t, 0 ≤ u t) (hvp : ∀ t, 0 ≤ v t)
    {M N : ℝ} (hub : ∀ t, ‖u t‖ ≤ M) (hvb : ∀ t, ‖v t‖ ≤ N)
    (heq : ∀ α : ℝ, 0 < α →
      (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * u t) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * v t) : EqOn u v (Ici (0 : ℝ)) := by
  let := discountedNonnegativeTimeMeasure_finite hu hup hub
  let := discountedNonnegativeTimeMeasure_finite hv hvp hvb
  have hm : discountedNonnegativeTimeMeasure u = discountedNonnegativeTimeMeasure v := by
    apply nonnegativeLaplace_measure_ext
    intro a
    rw [discountedNonnegativeTimeMeasure_laplace hu hup,
      discountedNonnegativeTimeMeasure_laplace hv hvp]
    exact heq ((a : ℝ) + 1) (by positivity)
  have hbase : discountedTimeMeasure u = discountedTimeMeasure v := by
    have h := congrArg (Measure.map (fun t : ℝ≥0 => (t : ℝ))) hm
    simpa only [discountedNonnegativeTimeMeasure_map_coe] using h
  have hden : discountedTimeDensity u =ᵐ[volume.restrict (Ioi (0 : ℝ))] discountedTimeDensity v :=
    (withDensity_eq_iff_of_sigmaFinite (discountedTimeDensity_measurable hu).aemeasurable
      (discountedTimeDensity_measurable hv).aemeasurable).mp hbase
  have hae : u =ᵐ[volume.restrict (Ioi (0 : ℝ))] v := by
    filter_upwards [hden] with t ht
    have he := congrArg ENNReal.toReal ht
    change (ENNReal.ofReal (Real.exp (-t) * u t)).toReal =
      (ENNReal.ofReal (Real.exp (-t) * v t)).toReal at he
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (hup t)),
      ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (hvp t))] at he
    exact mul_left_cancel₀ (Real.exp_ne_zero _) he
  have hon : EqOn u v (Ioi (0 : ℝ)) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hu.continuousOn hv.continuousOn
  simpa only [closure_Ioi] using hon.closure hu hv

theorem boundedContinuous_laplace_unique {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    {M N : ℝ} (hub : ∀ t, ‖u t‖ ≤ M) (hvb : ∀ t, ‖v t‖ ≤ N)
    (heq : ∀ α : ℝ, 0 < α →
      (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * u t) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * v t) : EqOn u v (Ici (0 : ℝ)) := by
  let K : ℝ := |M| + |N|
  have hK : 0 ≤ K := add_nonneg (abs_nonneg M) (abs_nonneg N)
  have huk (t : ℝ) : ‖u t‖ ≤ K := (hub t).trans (by dsimp [K]; linarith [le_abs_self M, abs_nonneg N])
  have hvk (t : ℝ) : ‖v t‖ ≤ K := (hvb t).trans (by dsimp [K]; linarith [le_abs_self N, abs_nonneg M])
  have hup (t : ℝ) : 0 ≤ u t + K := by
    have h := (abs_le.mp (show |u t| ≤ K from huk t)).1
    linarith
  have hvp (t : ℝ) : 0 ≤ v t + K := by
    have h := (abs_le.mp (show |v t| ≤ K from hvk t)).1
    linarith
  have hub' (t : ℝ) : ‖u t + K‖ ≤ 2 * K := by
    exact (norm_add_le _ _).trans (by rw [Real.norm_of_nonneg hK]; linarith [huk t])
  have hvb' (t : ℝ) : ‖v t + K‖ ≤ 2 * K := by
    exact (norm_add_le _ _).trans (by rw [Real.norm_of_nonneg hK]; linarith [hvk t])
  have heq' (α : ℝ) (hα : 0 < α) :
      (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * (u t + K)) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * (v t + K) := by
    simp_rw [mul_add]
    rw [integral_add (boundedDynkin_discounted_integrable hu hub hα)
      ((exp_neg_integrableOn_Ioi 0 hα).mul_const K),
      integral_add (boundedDynkin_discounted_integrable hv hvb hα)
      ((exp_neg_integrableOn_Ioi 0 hα).mul_const K), heq α hα]
  have hs := nonnegative_boundedContinuous_laplace_unique (hu.add continuous_const)
    (hv.add continuous_const) hup hvp hub' hvb' heq'
  intro t ht
  exact add_right_cancel (hs ht)

theorem boundedContinuous_nonnegativeTime_laplace_unique {u v : ℝ≥0 → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    {M N : ℝ} (hub : ∀ t, ‖u t‖ ≤ M) (hvb : ∀ t, ‖v t‖ ≤ N)
    (heq : ∀ α : ℝ, 0 < α →
      (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * u t.toNNReal) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * v t.toNNReal) : u = v := by
  have h := boundedContinuous_laplace_unique (hu.comp continuous_real_toNNReal)
    (hv.comp continuous_real_toNNReal) (fun t => hub t.toNNReal) (fun t => hvb t.toNNReal) heq
  funext t
  have he := h (show (t : ℝ) ∈ Ici (0 : ℝ) from t.property)
  simpa only [Function.comp_apply, Real.toNNReal_coe] using he

end TimeTraps.Probability

end
