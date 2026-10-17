module

public import TimeTraps.Probability.BrownianIntegralMaximal
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! The finite-grid maximal bound also applies to a nonempty finite set
of times. Sorting is explicit and preserves the actual finite maximum. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

def brownianIntegralFiniteMax (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (s : Finset ℝ≥0) (hs : s.Nonempty) (ω : Ω) : ℝ :=
  s.sup' hs (fun t => |brownianIntegralProcess hB f t ω|)

theorem brownianIntegralFiniteMax_eq_ordered (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (s : Finset ℝ≥0) (hs : s.Nonempty)
    {N : ℕ} (hcard : s.card = N + 1) (ω : Ω) :
    brownianIntegralFiniteMax hB f s hs ω =
      brownianIntegralGridMax hB f (s.orderEmbOfFin hcard) ω := by
  unfold brownianIntegralFiniteMax brownianIntegralGridMax
  apply le_antisymm
  · apply Finset.sup'_le
    intro t ht
    have ht' : t ∈ range (s.orderEmbOfFin hcard) := by
      rw [s.range_orderEmbOfFin hcard]
      exact ht
    obtain ⟨i, rfl⟩ := ht'
    exact Finset.le_sup' (fun i => |brownianIntegralProcess hB f (s.orderEmbOfFin hcard i) ω|)
      (Finset.mem_univ i)
  · apply Finset.sup'_le
    intro i _
    exact Finset.le_sup' (fun t => |brownianIntegralProcess hB f t ω|) (s.orderEmbOfFin_mem hcard i)

theorem brownianIntegralFiniteMax_memLp (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (s : Finset ℝ≥0) (hs : s.Nonempty) :
    MemLp (brownianIntegralFiniteMax hB f s hs) 2 P := by
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr hs).ne'
  have he : brownianIntegralFiniteMax hB f s hs =
      brownianIntegralGridMax hB f (s.orderEmbOfFin hN) :=
    funext (brownianIntegralFiniteMax_eq_ordered hB f s hs hN)
  rw [he]
  exact brownianIntegralGridMax_memLp hB f _

theorem brownianIntegralFiniteMax_le_norm (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (s : Finset ℝ≥0) (hs : s.Nonempty)
    (T : ℝ≥0) (hT : ∀ t ∈ s, t ≤ T) :
    (∫ ω, brownianIntegralFiniteMax hB f s hs ω ^ 2 ∂P) ≤
      4 * ‖brownianTimeCutoff B hBm P T f‖ ^ 2 := by
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr hs).ne'
  have he : brownianIntegralFiniteMax hB f s hs =
      brownianIntegralGridMax hB f (s.orderEmbOfFin hN) :=
    funext (brownianIntegralFiniteMax_eq_ordered hB f s hs hN)
  rw [he]
  exact brownianIntegralGridMax_le_norm hB f _ (s.orderEmbOfFin hN).monotone T
    (hT _ (s.orderEmbOfFin_mem hN (Fin.last N)))

end TimeTraps.Probability

end
