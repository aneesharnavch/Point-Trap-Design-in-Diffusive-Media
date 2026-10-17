module

public import TimeTraps.Interval.ReversibleResistanceWeakForm

@[expose] public section

/-! The actual reference solution with forcing equal to the time-change
speed pulls back to the original physical mean equation. Full weak
uniqueness identifies it with every independently specified physical
solution, including the paper's admissible design states. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Spectral

variable {n : ℕ}

theorem reversible_resistance_forced_pullback (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) {v : ℝ → ℝ}
    (hv : WeakForcedEquation (D.resistanceSpectralProblem hn κ hκ) D.medium.resistanceSpeed v) :
    WeakIntervalEquation D κ (fun x => v (D.medium.resistance x)) := by
  apply (reversible_resistance_weak_iff D hn κ hκ _).mpr
  have he := D.medium.resistance_profile_pullback v
  have hve : IntervalEnergy v 0 D.medium.resistanceLength := hv.energy
  refine ⟨hve.congr (by simpa only [uIcc_of_le D.medium.resistanceLength_pos.le] using he.symm), ?_⟩
  intro w hw
  have hc := intervalPointForm_congr 1 κ (fun i => D.medium.resistance (D.site i))
    D.medium.resistanceLength_pos.le
    (fun i => Ioo_subset_Icc_self (D.medium.resistance_interior (D.site_interior i)))
    he (fun _ _ => rfl : EqOn w w (Icc 0 D.medium.resistanceLength))
  exact hc.trans (hv.weak_form w hw)

noncomputable def OrderedMedium.resistanceMeanState (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) (x : ℝ) : ℝ :=
  (D.resistanceSpectralProblem hn κ hκ).forcedSolutionState D.medium.resistanceSpeed
    D.medium.resistanceSpeed_continuous.continuousOn (D.medium.resistance x)

theorem OrderedMedium.resistanceMeanState_weak (D : OrderedMedium n)
    (hn : 0 < n) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) :
    WeakIntervalEquation D κ (D.resistanceMeanState hn κ hκ) :=
  reversible_resistance_forced_pullback D hn κ hκ
    ((D.resistanceSpectralProblem hn κ hκ).forcedSolution_weak D.medium.resistanceSpeed
      D.medium.resistanceSpeed_continuous.continuousOn)

theorem WeakIntervalEquation.eq_resistanceMeanState {D : OrderedMedium n}
    (hn : 0 < n) {κ : Fin n → ℝ} (hκ : ∀ i, 0 < κ i) {u : ℝ → ℝ}
    (hu : WeakIntervalEquation D κ u) :
    EqOn u (D.resistanceMeanState hn κ hκ) (Icc D.source.left D.source.right) :=
  interval_weak_state_unique hu (D.resistanceMeanState_weak hn κ hκ)
    (fun i => (hκ i).le) ⟨⟨0, hn⟩, hκ _⟩

end TimeTraps.Interval
