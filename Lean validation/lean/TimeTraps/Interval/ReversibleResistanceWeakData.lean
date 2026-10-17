module

public import TimeTraps.Analysis.ReversibleResistanceSobolevForm
public import TimeTraps.Interval.WeakProblem
public import TimeTraps.Spectral.ReflectedForcedKinkOperator

@[expose] public section

/-! The reference point-interaction problem is built from the original
physical design by the actual resistance coordinate. Its diffusivity is
one, its contact strengths are unchanged, and its forcing is the actual
positive clock speed. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Spectral

variable {n : ℕ}

theorem IntervalMedium.resistance_interior (A : IntervalMedium) {x : ℝ}
    (hx : x ∈ Ioo A.source.left A.source.right) :
    A.resistance x ∈ Ioo 0 A.resistanceLength := by
  constructor
  · simpa only [A.resistance_left] using A.resistance_strictMono
      ⟨le_rfl, A.source.increasing.le⟩ (Ioo_subset_Icc_self hx) hx.1
  · simpa only [A.resistance_right] using A.resistance_strictMono
      (Ioo_subset_Icc_self hx) ⟨A.source.increasing.le, le_rfl⟩ hx.2

noncomputable def OrderedMedium.resistanceSpectralProblem (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) : SpectralProblem n where
  count_pos := hn
  length := D.medium.resistanceLength
  length_pos := D.medium.resistanceLength_pos
  diffusivity := 1
  diffusivity_pos := zero_lt_one
  site := fun i => D.medium.resistance (D.site i)
  site_strictMono := fun i j hij => D.medium.resistance_strictMono
    (Ioo_subset_Icc_self (D.site_interior i)) (Ioo_subset_Icc_self (D.site_interior j))
      (D.site_strictMono hij)
  site_interior := fun i => D.medium.resistance_interior (D.site_interior i)
  strength := κ
  strength_pos := hκ

theorem OrderedMedium.resistanceSpectralProblem_site (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) (i : Fin n) :
    (D.resistanceSpectralProblem hn κ hκ).site i = D.medium.resistance (D.site i) := rfl

theorem OrderedMedium.resistanceProfile_site (D : OrderedMedium n)
    (u : ℝ → ℝ) (i : Fin n) :
    D.medium.resistanceProfile u (D.medium.resistance (D.site i)) = u (D.site i) :=
  congrArg u (D.medium.resistanceInverse_resistance (Ioo_subset_Icc_self (D.site_interior i)))

end TimeTraps.Interval
