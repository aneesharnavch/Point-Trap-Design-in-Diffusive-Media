module

public import TimeTraps.Probability.BrownianPredictableSignCharacteristic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! A mixed characteristic identity is preserved under actual L2 convergence.
The multiplier may be any integrable complex random variable. An almost-sure
subsequence and dominated convergence suffice; neither independence nor a
Gaussian law is assumed for the limit. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem brownianRealChar_continuous (u : ℝ) : Continuous (brownianRealChar u) := by
  unfold brownianRealChar
  fun_prop

theorem brownianL2_mixed_char_eq_of_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (U : ℕ → Lp ℝ 2 P) (Y : Lp ℝ 2 P)
    (Z : Ω → ℂ) (hZ : Integrable Z P) (u : ℝ) (c : ℂ)
    (hlim : Tendsto U atTop (𝓝 Y))
    (he : ∀ n, (∫ ω, Z ω * brownianRealChar u (U n ω) ∂P) = c) :
    (∫ ω, Z ω * brownianRealChar u (Y ω) ∂P) = c := by
  obtain ⟨b, _, hb⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun ω => Z ω * brownianRealChar u (U (b n) ω)) P :=
    hZ.aestronglyMeasurable.mul
      (((brownianRealChar_measurable u).comp_aemeasurable
        (Lp.aestronglyMeasurable (U (b n))).aemeasurable).aestronglyMeasurable)
  have hbound (n : ℕ) : ∀ᵐ ω ∂P,
      ‖Z ω * brownianRealChar u (U (b n) ω)‖ ≤ ‖Z ω‖ := by
    filter_upwards [] with ω
    rw [norm_mul, brownianRealChar_norm, mul_one]
  have hp : ∀ᵐ ω ∂P, Tendsto
      (fun n => Z ω * brownianRealChar u (U (b n) ω)) atTop
        (𝓝 (Z ω * brownianRealChar u (Y ω))) := by
    filter_upwards [hb] with ω hω
    exact ((brownianRealChar_continuous u).continuousAt.tendsto.comp hω).const_mul (Z ω)
  have hd := tendsto_integral_of_dominated_convergence (fun ω => ‖Z ω‖) hm hZ.norm hbound hp
  simp only [he] at hd
  exact tendsto_nhds_unique hd tendsto_const_nhds

end TimeTraps.Probability
