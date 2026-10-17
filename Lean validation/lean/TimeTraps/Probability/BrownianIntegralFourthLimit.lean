module

public import TimeTraps.Probability.BrownianIntegralFourthMixed
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

/-! Fatou transfers fourth-moment bounds through the actual L2 integral
limit. Integrability of the fourth power of the limit is a conclusion. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem brownian_fourth_bound_of_ae_tendsto {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hf : ∀ n, MemLp (f n) 4 P) (hg : AEStronglyMeasurable g P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hb : ∀ᶠ n in atTop, (∫ ω, f n ω ^ 4 ∂P) ≤ R ^ 2) :
    MemLp g 4 P ∧ (∫ ω, g ω ^ 4 ∂P) ≤ R ^ 2 := by
  have hf2 (n : ℕ) := brownian_fourth_square_memLp (hf n)
  have he : ∀ᶠ n in atTop, eLpNorm (fun ω => f n ω ^ 2) 2 P ≤ ENNReal.ofReal R := by
    filter_upwards [hb] with n hn
    have hnorm : ‖(hf2 n).toLp (fun ω => f n ω ^ 2)‖ ≤ R := by
      apply (sq_le_sq₀ (norm_nonneg _) hR).mp
      rw [memLp_norm_toLp_sq]
      simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using hn
    rw [← Lp.enorm_toLp (hf2 n), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hnorm
  have hge : eLpNorm (fun ω => g ω ^ 2) 2 P ≤ ENNReal.ofReal R :=
    Lp.eLpNorm_le_of_ae_tendsto he (fun n => (hf2 n).aestronglyMeasurable)
      (hlim.mono (fun _ hω => hω.pow 2))
  have hg2 : MemLp (fun ω => g ω ^ 2) 2 P := ⟨hg.pow 2, hge.trans_lt (by finiteness)⟩
  have hi4 : Integrable (fun ω => g ω ^ 4) P := by
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using hg2.integrable_sq
  refine ⟨brownian_fourth_memLp_of_integrable hg hi4, ?_⟩
  have hnorm : ‖hg2.toLp (fun ω => g ω ^ 2)‖ ≤ R := by
    rw [Lp.norm_toLp]
    simpa only [ENNReal.toReal_ofReal hR] using
      ENNReal.toReal_mono (by finiteness : ENNReal.ofReal R ≠ ⊤) hge
  have hs := (sq_le_sq₀ (norm_nonneg _) hR).mpr hnorm
  rw [memLp_norm_toLp_sq] at hs
  simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using hs

theorem brownian_fourth_bound_of_ae_tendsto_varying {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    {c : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, MemLp (f n) 4 P)
    (hg : AEStronglyMeasurable g P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hb : ∀ n, (∫ ω, f n ω ^ 4 ∂P) ≤ c n) (hc : Tendsto c atTop (𝓝 C)) :
    MemLp g 4 P ∧ (∫ ω, g ω ^ 4 ∂P) ≤ C := by
  have he (ε : ℝ) (hε : 0 < ε) : MemLp g 4 P ∧ (∫ ω, g ω ^ 4 ∂P) ≤ C + ε := by
    have hpos : 0 ≤ C + ε := by positivity
    have hbound : ∀ᶠ n in atTop, (∫ ω, f n ω ^ 4 ∂P) ≤ (Real.sqrt (C + ε)) ^ 2 := by
      filter_upwards [hc.eventually (eventually_lt_nhds (by linarith : C < C + ε))] with n hn
      rw [Real.sq_sqrt hpos]
      exact (hb n).trans hn.le
    have h := brownian_fourth_bound_of_ae_tendsto (Real.sqrt_nonneg _) hf hg hlim hbound
    simpa only [Real.sq_sqrt hpos] using h
  refine ⟨(he 1 (by norm_num)).1, ?_⟩
  exact le_of_forall_pos_le_add (fun ε hε => (he ε hε).2)

theorem brownian_fourth_bound_of_L2_tendsto {F : ℕ → Lp ℝ 2 P} {G : Lp ℝ 2 P}
    {c : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, MemLp (F n) 4 P)
    (hlim : Tendsto F atTop (𝓝 G)) (hb : ∀ n, (∫ ω, F n ω ^ 4 ∂P) ≤ c n)
    (hc : Tendsto c atTop (𝓝 C)) : MemLp G 4 P ∧ (∫ ω, G ω ^ 4 ∂P) ≤ C := by
  obtain ⟨u, hu, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  exact brownian_fourth_bound_of_ae_tendsto_varying hC (fun n => hf (u n))
    (Lp.aestronglyMeasurable G) hAE (fun n => hb (u n)) (hc.comp hu.tendsto_atTop)

end TimeTraps.Probability
