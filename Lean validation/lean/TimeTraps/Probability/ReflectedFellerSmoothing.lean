module

public import TimeTraps.Probability.ReflectedFellerSeriesDerivative
public import TimeTraps.Probability.ReflectedFellerSmoothingRegularity

@[expose] public section

/-! Every continuous initial function evolves immediately into the full
C² Neumann class. The actual Feller trajectory satisfies the classical
heat equation in the open interval, with both reflecting slope traces.
No initial generator-domain or differentiability hypothesis is imposed. -/

namespace TimeTraps.Probability

open MeasureTheory Set

theorem reflectedFeller_positive_time_neumann (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 < t) :
    ∃ F : ReflectedNeumannC2 L,
      F.valueMap = reflectedFellerTimeOperator L hL D t f ∧
      HasDerivAt (fun s : ℝ => reflectedFellerTimeOperator L hL D s f) (D • F.curvatureMap) t := by
  obtain ⟨F, hf, hg⟩ := reflectedFeller_generator_exists_neumannC2 L hL D hD
    (reflectedFellerTimeOperator L hL D t f)
    (∑' n : ℕ, reflectedFellerHeatTermDerivative L hL D f n t)
    (reflectedFellerTimeOperator_generator L hL D hD f t ht)
  refine ⟨F, hf, ?_⟩
  rw [hg]
  exact reflectedFellerTimeOperator_hasDerivAt L hL D hD f t ht

theorem reflectedFeller_positive_time_boundary (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt (reflectedFellerExtension L hL (reflectedFellerTimeOperator L hL D t f))
      0 (Icc 0 L) 0 ∧
    HasDerivWithinAt (reflectedFellerExtension L hL (reflectedFellerTimeOperator L hL D t f))
      0 (Icc 0 L) L := by
  obtain ⟨F, hf, _⟩ := reflectedFeller_positive_time_neumann L hL D hD f t ht
  constructor
  · simpa only [hf, F.neumann_left] using
      F.extension_within_derivative hL 0 ⟨le_refl 0, hL.le⟩
  · simpa only [hf, F.neumann_right] using
      F.extension_within_derivative hL L ⟨hL.le, le_refl L⟩

theorem reflectedFeller_positive_time_heatEquation (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 < t) (x : ℝ) (hx : x ∈ Ioo 0 L) :
    HasDerivAt (fun s : ℝ => reflectedFellerTimeOperator L hL D s f ⟨x, hx.1.le, hx.2.le⟩)
      (D * deriv (deriv (reflectedFellerExtension L hL (reflectedFellerTimeOperator L hL D t f))) x) t := by
  obtain ⟨F, hf, hd⟩ := reflectedFeller_positive_time_neumann L hL D hD f t ht
  have he := (ContinuousMap.evalCLM ℝ (⟨x, hx.1.le, hx.2.le⟩ : Icc (0 : ℝ) L)).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s : ℝ => reflectedFellerTimeOperator L hL D s f ⟨x, hx.1.le, hx.2.le⟩)
    (D * F.curvature x) t at he
  have hcurv := F.extension_second_derivative hL x hx
  rw [hf] at hcurv
  rw [hcurv]
  exact he

end TimeTraps.Probability
