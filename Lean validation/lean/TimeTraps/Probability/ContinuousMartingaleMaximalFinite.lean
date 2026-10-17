module

public import TimeTraps.Probability.ContinuousMartingaleMaximalGrid
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! Finite-set maxima inherit the constant-four Doob bound by sorting
the actual times. The terminal time is included explicitly. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {M : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}

noncomputable def martingaleFiniteMax (M : ℝ≥0 → Ω → ℝ)
    (s : Finset ℝ≥0) (hs : s.Nonempty) (ω : Ω) : ℝ :=
  s.sup' hs (fun t => |M t ω|)

theorem martingaleFiniteMax_eq_ordered (s : Finset ℝ≥0) (hs : s.Nonempty)
    {N : ℕ} (hcard : s.card = N + 1) (ω : Ω) :
    martingaleFiniteMax M s hs ω = martingaleGridMax M (s.orderEmbOfFin hcard) ω := by
  unfold martingaleFiniteMax martingaleGridMax
  apply le_antisymm
  · apply Finset.sup'_le
    intro t ht
    have ht' : t ∈ range (s.orderEmbOfFin hcard) := by
      rw [s.range_orderEmbOfFin hcard]
      exact ht
    obtain ⟨i, rfl⟩ := ht'
    exact Finset.le_sup' (fun i => |M (s.orderEmbOfFin hcard i) ω|) (Finset.mem_univ i)
  · apply Finset.sup'_le
    intro i _
    exact Finset.le_sup' (fun t => |M t ω|) (s.orderEmbOfFin_mem hcard i)

theorem martingaleFiniteMax_memLp (hM2 : ∀ t, MemLp (M t) 2 μ)
    (s : Finset ℝ≥0) (hs : s.Nonempty) : MemLp (martingaleFiniteMax M s hs) 2 μ := by
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr hs).ne'
  have he : martingaleFiniteMax M s hs = martingaleGridMax M (s.orderEmbOfFin hN) :=
    funext (martingaleFiniteMax_eq_ordered s hs hN)
  rw [he]
  exact martingaleGridMax_memLp hM2 _

theorem martingaleFiniteMax_second_moment [IsFiniteMeasure μ] (hM : Martingale M 𝓕 μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (s : Finset ℝ≥0) (hs : s.Nonempty)
    (T : ℝ≥0) (hmem : T ∈ s) (hT : ∀ t ∈ s, t ≤ T) :
    (∫ ω, martingaleFiniteMax M s hs ω ^ 2 ∂μ) ≤ 4 * ∫ ω, M T ω ^ 2 ∂μ := by
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr hs).ne'
  have he : martingaleFiniteMax M s hs = martingaleGridMax M (s.orderEmbOfFin hN) :=
    funext (martingaleFiniteMax_eq_ordered s hs hN)
  have ht : s.orderEmbOfFin hN (Fin.last N) = T := by
    apply le_antisymm (hT _ (s.orderEmbOfFin_mem hN (Fin.last N)))
    have hTr : T ∈ range (s.orderEmbOfFin hN) := by
      rw [s.range_orderEmbOfFin hN]
      exact hmem
    obtain ⟨i, rfl⟩ := hTr
    exact (s.orderEmbOfFin hN).monotone (Fin.le_last i)
  rw [he]
  simpa only [ht] using martingaleGridMax_second_moment hM hM2
    (s.orderEmbOfFin hN) (s.orderEmbOfFin hN).monotone

end TimeTraps.Probability
