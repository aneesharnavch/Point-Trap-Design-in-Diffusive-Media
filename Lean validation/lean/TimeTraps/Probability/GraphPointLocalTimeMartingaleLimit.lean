module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! Closedness of real conditional expectation in the actual L2 spaces.
The proof uses the continuous orthogonal projection already identified
with conditional expectation, rather than a martingale-limit premise. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped Topology

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem pointMartingale_condExp_closed_L2 [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {F G : ℕ → Lp ℝ 2 μ} {f g : Lp ℝ 2 μ}
    (hF : Tendsto F atTop (𝓝 f)) (hG : Tendsto G atTop (𝓝 g))
    (hC : ∀ n, μ[F n | m] =ᵐ[μ] G n) : μ[f | m] =ᵐ[μ] g := by
  let C : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (lpMeas ℝ ℝ m 2 μ).subtypeL.comp (condExpL2 ℝ ℝ hm)
  have hCe (u : Lp ℝ 2 μ) : C u =ᵐ[μ] μ[u | m] := by
    simpa only [C, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Lp.toLp_coeFn] using
      (Lp.memLp u).condExpL2_ae_eq_condExp (𝕜 := ℝ) hm
  have he (n : ℕ) : C (F n) = G n := Lp.ext ((hCe (F n)).trans (hC n))
  have hlim := C.continuous.continuousAt.tendsto.comp hF
  have heq : C f = g := tendsto_nhds_unique hlim (hG.congr' (Eventually.of_forall (fun n => (he n).symm)))
  exact (hCe f).symm.trans (by rw [heq])

end TimeTraps.Probability
