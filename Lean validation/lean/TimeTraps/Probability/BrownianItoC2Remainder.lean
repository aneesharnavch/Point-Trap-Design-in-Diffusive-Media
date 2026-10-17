module

public import TimeTraps.Analysis.ItoTaylorC2
public import TimeTraps.Probability.ContinuousMonotoneQuadraticVariation
public import TimeTraps.Probability.BrownianQuadraticVariationAlmostSure
public import TimeTraps.Probability.BrownianItoTaylorSum

@[expose] public section

/-! C2 Taylor errors vanish along every continuous dyadic path whose
quadratic variation converges. Compact path ranges supply the local
curvature modulus, so no third derivative or global curvature modulus
is needed. The actual Brownian application holds almost surely. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem dyadicPath_increments_eventually_small (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : ContinuousOn f (Icc 0 T)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ n),
      |f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc)| < ε := by
  have hmesh : Tendsto (fun n : ℕ => T.val / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul T.val
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with n hn i
  have hd : dist (brownianDyadicGrid T n i.succ) (brownianDyadicGrid T n i.castSucc) < δ := by
    change |(brownianDyadicGrid T n i.succ).val - (brownianDyadicGrid T n i.castSucc).val| < δ
    rw [brownianDyadicGrid_gap]
    exact hn
  exact hc _ (brownianDyadicGrid_mem_Icc T n i.succ)
    _ (brownianDyadicGrid_mem_Icc T n i.castSucc) hd

theorem dyadicItoTaylorSum_c2_tendsto {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (f : ℝ≥0 → ℝ) (T : ℝ≥0) (hf : ContinuousOn f (Icc 0 T))
    {A : ℝ} (hQV : Tendsto (dyadicPathQV f T) atTop (𝓝 A)) :
    Tendsto (fun n : ℕ => ∑ i : Fin (2 ^ n),
      itoTaylorRemainder F (f (brownianDyadicGrid T n i.castSucc)) (f (brownianDyadicGrid T n i.succ)))
      atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hrange (n : ℕ) (i : Fin (2 ^ n + 1)) : f (brownianDyadicGrid T n i) ∈ Icc (-R) R := by
    have hb := hR _ (brownianDyadicGrid_mem_Icc T n i)
    exact abs_le.mp hb
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := |A| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let η : ℝ := ε / C
  have hη : 0 < η := div_pos hε hC
  obtain ⟨δ, hδ, hc⟩ := itoTaylorRemainder_c2_compact hF (-R) R hη
  have hA : A < C := by dsimp [C]; linarith [le_abs_self A]
  filter_upwards [dyadicPath_increments_eventually_small f T hf hδ,
    hQV.eventually (gt_mem_nhds hA)] with n hn hq
  rw [Real.dist_eq, sub_zero]
  calc
    _ ≤ ∑ i : Fin (2 ^ n), |itoTaylorRemainder F
        (f (brownianDyadicGrid T n i.castSucc)) (f (brownianDyadicGrid T n i.succ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (2 ^ n), η *
        (f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact hc _ (hrange n i.castSucc) _ (hrange n i.succ) (hn i)
    _ = η * dyadicPathQV f T n := by
      rw [← Finset.mul_sum]
      rfl
    _ < ε := by
      have he : η * C = ε := div_mul_cancel₀ ε hC.ne'
      exact (mul_lt_mul_of_pos_left hq hη).trans_eq he

theorem brownianItoTaylorDyadic_c2_ae_tendsto {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsBrownianReal B P)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => brownianItoTaylorSum B F (brownianDyadicGrid T n) ω) atTop (𝓝 0) := by
  filter_upwards [hB.cont, brownianDyadicQV_ae_tendsto hB.toIsPreBrownianReal T] with ω hc hq
  exact dyadicItoTaylorSum_c2_tendsto hF (fun t => B t ω) T hc.continuousOn hq

end TimeTraps.Probability
