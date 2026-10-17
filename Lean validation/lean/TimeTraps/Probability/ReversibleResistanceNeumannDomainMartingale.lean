module

public import TimeTraps.Probability.ReversibleResistanceNeumannDomain

@[expose] public section

/-! The constructed physical process satisfies the Neumann martingale
problem for every continuous physical divergence-domain test. The value
and generator in the compensated process are the original physical
functions, with no coefficient derivatives or reference-coordinate
formula assumed of the caller. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal

variable {A : IntervalMedium}

noncomputable def reversibleNeumannDynkin (H : ReversibleNeumannTest A)
    (x : ℝ) (t : ℝ≥0) (ω : BrownianCompletedSample) : ℝ :=
  H.value (reversibleResistancePath A x t ω) - H.value x -
    ∫ r in (0 : ℝ)..t.val, H.generator (reversibleResistancePath A x r.toNNReal ω)

theorem reversibleNeumannDynkin_eq_reference (H : ReversibleNeumannTest A)
    {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right) (t : ℝ≥0) (ω : BrownianCompletedSample) :
    reversibleNeumannDynkin H x t ω = reversibleResistanceNeumannDynkin A H.reference x t ω := by
  unfold reversibleNeumannDynkin reversibleResistanceNeumannDynkin
  rw [H.reference_value (reversibleResistancePath_mem A x t ω), H.reference_value hx]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _hr
  exact (H.reference_generator (reversibleResistancePath_mem A x r.toNNReal ω)).symm

theorem reversibleNeumannDynkin_martingale (H : ReversibleNeumannTest A)
    {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right) :
    Martingale (reversibleNeumannDynkin H x) (reversibleResistanceFiltration A x)
      brownianCompletedMeasure := by
  have he : reversibleNeumannDynkin H x = reversibleResistanceNeumannDynkin A H.reference x :=
    funext (fun t => funext (fun ω => reversibleNeumannDynkin_eq_reference H hx t ω))
  rw [he]
  exact reversibleResistanceNeumannDynkin_martingale A H.reference hx

theorem reversibleNeumannDynkin_condExp (H : ReversibleNeumannTest A)
    {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right) {s t : ℝ≥0} (hst : s ≤ t) :
    brownianCompletedMeasure[reversibleNeumannDynkin H x t | reversibleResistanceFiltration A x s]
      =ᵐ[brownianCompletedMeasure] reversibleNeumannDynkin H x s :=
  (reversibleNeumannDynkin_martingale H hx).2 s t hst

theorem reversibleNeumannDynkin_original_integrable_mean (H : ReversibleNeumannTest A)
    {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right) (t : ℝ≥0) :
    Integrable (fun ω : ℕ → ℝ => reversibleNeumannDynkin H x t ω) brownianDyadicMeasure ∧
      (∫ ω : ℕ → ℝ, reversibleNeumannDynkin H x t ω ∂brownianDyadicMeasure) = 0 := by
  have he : (fun ω : ℕ → ℝ => reversibleNeumannDynkin H x t ω) =
      fun ω => reversibleResistanceNeumannDynkin A H.reference x t ω :=
    funext (fun ω => reversibleNeumannDynkin_eq_reference H hx t ω)
  rw [he]
  exact reversibleResistanceNeumannDynkin_original_integrable_mean A H.reference hx t

end TimeTraps.Probability
