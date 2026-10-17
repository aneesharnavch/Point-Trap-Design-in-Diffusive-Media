module

public import TimeTraps.Interval.ReversibleResistanceWeakData

@[expose] public section

/-! Exact transport of the physical energy and every finite contact
pairing. The resistance coordinate changes the diffusion coefficient to
one and leaves the physical contact strengths unchanged. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Spectral

variable {n : ℕ}

theorem OrderedMedium.resistance_point_form (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u D.source.left D.source.right)
    (hv : IntervalEnergy v D.source.left D.source.right) :
    (∫ x in D.source.left..D.source.right, D.conductance x * deriv u x * deriv v x) +
      (∑ i, κ i * u (D.site i) * v (D.site i)) =
        intervalPointForm (D.resistanceSpectralProblem hn κ hκ).diffusivity
          (D.resistanceSpectralProblem hn κ hκ).strength
          (D.resistanceSpectralProblem hn κ hκ).site 0 D.medium.resistanceLength
          (D.medium.resistanceProfile u) (D.medium.resistanceProfile v) := by
  change _ = 1 * (∫ y in (0 : ℝ)..D.medium.resistanceLength,
    deriv (D.medium.resistanceProfile u) y * deriv (D.medium.resistanceProfile v) y) +
      ∑ i, κ i * D.medium.resistanceProfile u (D.medium.resistance (D.site i)) *
        D.medium.resistanceProfile v (D.medium.resistance (D.site i))
  rw [one_mul, ← D.medium.resistance_h1_bilinear hu hv]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [D.resistanceProfile_site u i, D.resistanceProfile_site v i]

theorem reversible_resistance_weak_iff (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) (u : ℝ → ℝ) :
    WeakIntervalEquation D κ u ↔
      WeakForcedEquation (D.resistanceSpectralProblem hn κ hκ) D.medium.resistanceSpeed
        (D.medium.resistanceProfile u) := by
  constructor
  · intro hu
    refine ⟨(D.medium.resistance_h1_profile hu.energy).1, ?_⟩
    intro v hv
    have hvp := (D.medium.resistance_h1_pullback hv).1
    have htv := D.medium.resistance_profile_pullback v
    have hf := D.resistance_point_form hn κ hκ hu.energy hvp
    dsimp only [OrderedMedium.resistanceSpectralProblem] at hf
    have ht := intervalPointForm_congr 1 κ (fun i => D.medium.resistance (D.site i))
      D.medium.resistanceLength_pos.le
      (fun i => Ioo_subset_Icc_self (D.medium.resistance_interior (D.site_interior i)))
      (u := D.medium.resistanceProfile u) (v := D.medium.resistanceProfile u)
      (w := D.medium.resistanceProfile (fun x => v (D.medium.resistance x))) (f := v)
      (fun _ _ => rfl) htv
    change intervalPointForm 1 κ (fun i => D.medium.resistance (D.site i)) 0 D.medium.resistanceLength
      (D.medium.resistanceProfile u) v = ∫ y in (0 : ℝ)..D.medium.resistanceLength,
        D.medium.resistanceSpeed y * v y
    rw [← ht, ← hf, hu.weak_form _ hvp]
    refine (D.medium.resistance_forcing_integral (fun x => v (D.medium.resistance x))).trans ?_
    apply intervalIntegral.integral_congr_Ioo_of_le D.medium.resistanceLength_pos.le
    intro y hy
    exact congrArg (fun a : ℝ => D.medium.resistanceSpeed y * a) (htv (Ioo_subset_Icc_self hy))
  · intro hu
    have hue := (D.medium.resistance_h1_iff u).mpr hu.energy
    refine ⟨hue, ?_⟩
    intro v hv
    exact (D.resistance_point_form hn κ hκ hue hv).trans
      ((hu.weak_form (D.medium.resistanceProfile v) (D.medium.resistance_h1_profile hv).1).trans
        (D.medium.resistance_forcing_integral v).symm)

end TimeTraps.Interval
