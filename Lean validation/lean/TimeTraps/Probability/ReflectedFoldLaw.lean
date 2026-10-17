module

public import TimeTraps.Probability.ReflectedGaussianKernel

@[expose] public section

/-! Folding symmetric additive noise depends on the starting point only
through its folded value. The argument uses the exact two lattice fibres,
periodicity and reflection symmetry. It applies to arbitrary symmetric
measures and, in particular, to centered Gaussians of any variance,
including the zero-variance Dirac law. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TimeTraps.Analysis
open scoped NNReal

theorem reflectedFold_shift_map_of_symmetric (L : ℝ) (hL : 0 < L)
    (μ : Measure ℝ) (hsym : μ.map (fun z => -z) = μ) (x : ℝ) :
    μ.map (fun z => reflectedFold L (x + z)) =
      μ.map (fun z => reflectedFold L (reflectedFold L x + z)) := by
  rcases (reflectedFold_eq_iff_lattice L hL x (reflectedFold L x)
    (reflectedFold_mem L hL x)).mp rfl with ⟨k, hk | hk⟩
  · apply Measure.map_congr
    filter_upwards [] with z
    calc
      reflectedFold L (x + z) = reflectedFold L ((reflectedFold L x + z) + k * (2 * L)) :=
        congrArg (reflectedFold L) (by linarith [hk])
      _ = reflectedFold L (reflectedFold L x + z) := reflectedFold_int_period L _ k
  · have he (z : ℝ) : reflectedFold L (x + z) = reflectedFold L (reflectedFold L x + -z) := by
      calc
        reflectedFold L (x + z) =
            reflectedFold L (-(reflectedFold L x + -z) + k * (2 * L)) :=
          congrArg (reflectedFold L) (by linarith [hk])
        _ = reflectedFold L (-(reflectedFold L x + -z)) := reflectedFold_int_period L _ k
        _ = reflectedFold L (reflectedFold L x + -z) := reflectedFold_neg L _
    calc
      μ.map (fun z => reflectedFold L (x + z)) =
          μ.map ((fun z => reflectedFold L (reflectedFold L x + z)) ∘ fun z => -z) :=
        Measure.map_congr (Filter.Eventually.of_forall he)
      _ = (μ.map (fun z => -z)).map (fun z => reflectedFold L (reflectedFold L x + z)) :=
        (Measure.map_map ((reflectedFold_measurable L).comp (measurable_const.add measurable_id))
          measurable_neg).symm
      _ = μ.map (fun z => reflectedFold L (reflectedFold L x + z)) := by rw [hsym]

theorem reflectedGaussianLaw_centered (L x : ℝ) (v : ℝ≥0) :
    reflectedGaussianLaw L x v =
      (gaussianReal 0 v).map (fun z => reflectedFold L (x + z)) := by
  have hshift : (gaussianReal 0 v).map (fun z => x + z) = gaussianReal x v := by
    simpa only [zero_add] using gaussianReal_map_const_add (μ := 0) (v := v) x
  rw [reflectedGaussianLaw, ← hshift]
  exact Measure.map_map (reflectedFold_measurable L)
    (show Measurable (fun z : ℝ => x + z) from measurable_const.add measurable_id)

theorem reflectedGaussianLaw_fold_start (L : ℝ) (hL : 0 < L) (x : ℝ) (v : ℝ≥0) :
    reflectedGaussianLaw L x v = reflectedGaussianLaw L (reflectedFold L x) v := by
  rw [reflectedGaussianLaw_centered, reflectedGaussianLaw_centered]
  apply reflectedFold_shift_map_of_symmetric L hL
  simpa only [neg_zero] using gaussianReal_map_neg (μ := 0) (v := v)

theorem reflectedGaussianLaw_eq_of_fold_eq (L : ℝ) (hL : 0 < L) {x y : ℝ}
    (hxy : reflectedFold L x = reflectedFold L y) (v : ℝ≥0) :
    reflectedGaussianLaw L x v = reflectedGaussianLaw L y v := by
  rw [reflectedGaussianLaw_fold_start L hL x, reflectedGaussianLaw_fold_start L hL y, hxy]

end TimeTraps.Probability
