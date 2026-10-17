module

public import TimeTraps.Probability.ReflectedFoldLaw
public import TimeTraps.Probability.IndependentNoiseConditional

@[expose] public section

/-! Bounded Borel conditional transition tests for a folded past-measurable
position plus independent centered Gaussian noise. The conditional law is
expressed using the folded present position; no Markov property is inferred
from marginal distributions alone. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

theorem reflectedGaussianLaw_integral_centered_fold (L : ℝ) (hL : 0 < L)
    (x : ℝ) (v : ℝ≥0) {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ z, g (reflectedFold L (x + z)) ∂gaussianReal 0 v) =
      ∫ y, g y ∂reflectedGaussianLaw L (reflectedFold L x) v := by
  calc
    _ = ∫ y, g y ∂reflectedGaussianLaw L x v := by
      rw [reflectedGaussianLaw_centered]
      exact (integral_map
        ((reflectedFold_measurable L).comp (show Measurable (fun z : ℝ => x + z) from
          measurable_const.add measurable_id)).aemeasurable hg.aestronglyMeasurable).symm
    _ = _ := congrArg (fun μ : Measure ℝ => ∫ y, g y ∂μ) (reflectedGaussianLaw_fold_start L hL x v)

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem reflectedFold_condExp_gaussian (hm : m ≤ mΩ) {Y Z : Ω → ℝ}
    (hY : Measurable[m] Y) (hZ : Measurable Z) {v : ℝ≥0}
    (hLaw : HasLaw Z (gaussianReal 0 v) P)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) m P)
    (L : ℝ) (hL : 0 < L) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) :
    P[fun ω => g (reflectedFold L (Y ω + Z ω)) | m] =ᵐ[P]
      fun ω => ∫ y, g y ∂reflectedGaussianLaw L (reflectedFold L (Y ω)) v := by
  have : IsProbabilityMeasure P := hLaw.isProbabilityMeasure
  have h := independentNoise_condExp_bounded hm hY hZ hind
    (hg.comp ((reflectedFold_measurable L).comp (measurable_fst.add measurable_snd)))
    (fun p => hb (reflectedFold L (p.1 + p.2)))
  refine h.trans ?_
  filter_upwards [] with ω
  rw [hLaw.map_eq]
  exact reflectedGaussianLaw_integral_centered_fold L hL (Y ω) v hg

end TimeTraps.Probability
