module

public import TimeTraps.Spectral.NetworkWeakState
public import TimeTraps.Analysis.IntervalEnergyLocal

@[expose] public section

/-! Weak network equations depend only on the functions on their closed
physical arcs. Values of a representative outside those arcs are irrelevant. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] {P : SpectralNetwork V E} {ev : ℝ}

theorem NetworkWeakEigenEquation.congr {U : V → ℝ} {u v : E → ℝ → ℝ}
    (h : NetworkWeakEigenEquation P ev U u)
    (huv : ∀ e, EqOn (u e) (v e) (Icc 0 (P.length e))) : NetworkWeakEigenEquation P ev U v := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro e
      apply (h.energy.edge_energy e).congr
      simpa only [SpectralNetwork.geometry, uIcc_of_le (P.length_pos e).le] using huv e
    · intro e
      exact (huv e ⟨le_rfl, (P.length_pos e).le⟩).symm.trans (h.energy.tail_value e)
    · intro e
      exact (huv e ⟨(P.length_pos e).le, le_rfl⟩).symm.trans (h.energy.head_value e)
  · intro W w hw
    have hd : (∑ e, ∫ x in (0 : ℝ)..P.length e, P.diffusivity * deriv (v e) x * deriv (w e) x) =
        ∑ e, ∫ x in (0 : ℝ)..P.length e, P.diffusivity * deriv (u e) x * deriv (w e) x := by
      apply Finset.sum_congr rfl
      intro e _
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      have hx' : x ∈ Ioo 0 (P.length e) := by simpa only [uIoo_of_le (P.length_pos e).le] using hx
      have he := (((huv e).mono Ioo_subset_Icc_self).deriv isOpen_Ioo) hx'
      dsimp only
      rw [he]
    have hm : (∑ e, ∫ x in (0 : ℝ)..P.length e, v e x * w e x) =
        ∑ e, ∫ x in (0 : ℝ)..P.length e, u e x * w e x := by
      apply Finset.sum_congr rfl
      intro e _
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc 0 (P.length e) := by simpa only [uIcc_of_le (P.length_pos e).le] using hx
      dsimp only
      rw [huv e hx']
    rw [hd, hm]
    exact h.weak_form W w hw

end TimeTraps.Spectral
