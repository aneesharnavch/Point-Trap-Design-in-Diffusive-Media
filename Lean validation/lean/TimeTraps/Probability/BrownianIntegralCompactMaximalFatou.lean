module

public import TimeTraps.Analysis.IntegralCauchySchwarz
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

/-! Fatou's lemma preserves a uniform real second-moment bound under
almost-everywhere convergence. No integrability of the limit is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory Filter
open scoped ENNReal Topology

theorem compactMaximal_memLp_of_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ n, MemLp (f n) 2 P) (hg : AEStronglyMeasurable g P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hbound : ∀ n, (∫ ω, f n ω ^ 2 ∂P) ≤ R ^ 2) :
    MemLp g 2 P ∧ (∫ ω, g ω ^ 2 ∂P) ≤ R ^ 2 := by
  have hn : ∀ n, ‖(hf n).toLp (f n)‖ ≤ R := by
    intro n
    apply (sq_le_sq₀ (norm_nonneg _) hR).mp
    rw [TimeTraps.Analysis.memLp_norm_toLp_sq]
    exact hbound n
  have he : ∀ n, eLpNorm (f n) 2 P ≤ ENNReal.ofReal R := by
    intro n
    rw [← Lp.enorm_toLp (hf n), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hn n)
  have hge : eLpNorm g 2 P ≤ ENNReal.ofReal R :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall he) (fun n => (hf n).1) hlim
  have hg2 : MemLp g 2 P := ⟨hg, hge.trans_lt (by finiteness)⟩
  have hgn : ‖hg2.toLp g‖ ≤ R := by
    rw [Lp.norm_toLp]
    simpa only [ENNReal.toReal_ofReal hR] using
      ENNReal.toReal_mono (by finiteness : ENNReal.ofReal R ≠ ⊤) hge
  refine ⟨hg2, ?_⟩
  rw [← TimeTraps.Analysis.memLp_norm_toLp_sq hg2]
  exact (sq_le_sq₀ (norm_nonneg _) hR).mpr hgn

end TimeTraps.Probability
