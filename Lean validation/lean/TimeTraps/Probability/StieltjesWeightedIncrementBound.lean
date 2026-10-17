module

public import TimeTraps.Probability.DyadicWeightedIncrementStieltjes

@[expose] public section

/-! The finite product identity controls every weighted increment sum by
three times a compact bound for its path, when the increasing loss of
weight takes values in [0,1]. No variation bound on the path is required. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem dyadicStieltjesRightSum_abs_le (K : StieltjesFunction ℝ)
    (g : ℝ≥0 → ℝ) (T : ℝ≥0) {R : ℝ}
    (hg : ∀ t ∈ Icc 0 T, |g t| ≤ R) (n : ℕ) :
    |dyadicStieltjesRightSum K g T n| ≤ (K (T : ℝ) - K 0) * R := by
  have hinc (i : Fin (2 ^ n)) : 0 ≤ K ((brownianDyadicGrid T n i.succ) : ℝ) -
      K ((brownianDyadicGrid T n i.castSucc) : ℝ) :=
    sub_nonneg.mpr (K.mono (brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i)))
  have htel : (∑ i : Fin (2 ^ n),
      (K ((brownianDyadicGrid T n i.succ) : ℝ) - K ((brownianDyadicGrid T n i.castSucc) : ℝ))) =
      K (T : ℝ) - K 0 := by
    simpa only [brownianDyadicGrid_last, brownianDyadicGrid_zero, NNReal.coe_zero] using
      finite_sum_increments (fun i : Fin (2 ^ n + 1) => K ((brownianDyadicGrid T n i) : ℝ))
  calc
    _ ≤ ∑ i : Fin (2 ^ n), |(K ((brownianDyadicGrid T n i.succ) : ℝ) -
        K ((brownianDyadicGrid T n i.castSucc) : ℝ)) * g (brownianDyadicGrid T n i.succ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (2 ^ n), (K ((brownianDyadicGrid T n i.succ) : ℝ) -
        K ((brownianDyadicGrid T n i.castSucc) : ℝ)) * R := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hinc i)]
      exact mul_le_mul_of_nonneg_left (hg _ (brownianDyadicGrid_mem_Icc T n i.succ)) (hinc i)
    _ = _ := by rw [← Finset.sum_mul, htel]

theorem dyadicWeightedIncrement_loss_bound (K : StieltjesFunction ℝ)
    (g : ℝ≥0 → ℝ) (T : ℝ≥0) {R : ℝ}
    (hK : ∀ t ∈ Icc 0 T, 0 ≤ K (t : ℝ) ∧ K (t : ℝ) ≤ 1)
    (hg : ∀ t ∈ Icc 0 T, |g t| ≤ R) (n : ℕ) :
    |dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) g T n| ≤ 3 * R := by
  have hT := hK T ⟨zero_le, le_rfl⟩
  have h0 := hK 0 ⟨le_rfl, zero_le⟩
  change 0 ≤ K 0 ∧ K 0 ≤ 1 at h0
  have hgT := hg T ⟨zero_le, le_rfl⟩
  have hg0 := hg 0 ⟨le_rfl, zero_le⟩
  have hR : 0 ≤ R := (abs_nonneg _).trans hg0
  have hbT : |(1 - K (T : ℝ)) * g T| ≤ R := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hT.2)]
    calc
      _ ≤ (1 - K (T : ℝ)) * R := mul_le_mul_of_nonneg_left hgT (sub_nonneg.mpr hT.2)
      _ ≤ R := by nlinarith [hT.1]
  have hb0 : |(1 - K 0) * g 0| ≤ R := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr h0.2)]
    calc
      _ ≤ (1 - K 0) * R := mul_le_mul_of_nonneg_left hg0 (sub_nonneg.mpr h0.2)
      _ ≤ R := by nlinarith [h0.1]
  have hbS : |dyadicStieltjesRightSum K g T n| ≤ R := by
    apply (dyadicStieltjesRightSum_abs_le K g T hg n).trans
    nlinarith [hT.2, h0.1]
  have he : dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) g T n =
      ((1 - K (T : ℝ)) * g T - (1 - K 0) * g 0) + dyadicStieltjesRightSum K g T n := by
    have h := dyadicWeightedIncrement_product_identity K g 1 T n
    change (1 - K (T : ℝ)) * g T - (1 - K 0) * g 0 =
      dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) g T n - dyadicStieltjesRightSum K g T n at h
    linarith
  rw [he]
  calc
    _ ≤ |(1 - K (T : ℝ)) * g T - (1 - K 0) * g 0| + |dyadicStieltjesRightSum K g T n| := abs_add_le _ _
    _ ≤ (|(1 - K (T : ℝ)) * g T| + |(1 - K 0) * g 0|) + |dyadicStieltjesRightSum K g T n| :=
      add_le_add (by simpa only [Real.norm_eq_abs] using
        (norm_sub_le ((1 - K (T : ℝ)) * g T) ((1 - K 0) * g 0))) le_rfl
    _ ≤ 3 * R := by linarith

theorem dyadicWeightedIncrement_loss_tendsto (K : StieltjesFunction ℝ)
    (g : ℝ≥0 → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    Tendsto (dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) g T) atTop
      (𝓝 (((1 - K (T : ℝ)) * g T - (1 - K 0) * g 0) +
        ∫ r in Ioc (0 : ℝ) (T : ℝ), g r.toNNReal ∂K.measure)) := by
  have he (n : ℕ) : dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) g T n =
      ((1 - K (T : ℝ)) * g T - (1 - K 0) * g 0) + dyadicStieltjesRightSum K g T n := by
    have h := dyadicWeightedIncrement_product_identity K g 1 T n
    change (1 - K (T : ℝ)) * g T - (1 - K 0) * g 0 =
      dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) g T n - dyadicStieltjesRightSum K g T n at h
    linarith
  rw [show dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) g T =
    (fun n => ((1 - K (T : ℝ)) * g T - (1 - K 0) * g 0) + dyadicStieltjesRightSum K g T n) from funext he]
  exact tendsto_const_nhds.add (dyadicStieltjesRightSum_tendsto K g hg T)

end TimeTraps.Probability
