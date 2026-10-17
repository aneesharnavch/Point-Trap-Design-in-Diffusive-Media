module

public import TimeTraps.Probability.DyadicWeightedQuadraticVariationData
public import TimeTraps.Probability.BrownianItoDriftContinuousAdapted

@[expose] public section

/-! Continuous time weights admit uniform coarse dyadic approximation.
The ordinary left time sums converge to the actual interval integral;
these are deterministic statements and impose no differentiability on
the weight. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

noncomputable def dyadicTimeLeftSum (g : ℝ≥0 → ℝ) (T : ℝ≥0) (m : ℕ) : ℝ :=
  ∑ j : Fin (2 ^ m), ((brownianDyadicGrid T m j.succ).val -
    (brownianDyadicGrid T m j.castSucc).val) * g (brownianDyadicGrid T m j.castSucc)

theorem dyadicTimeLeftSum_tendsto (g : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hg : ContinuousOn g (Icc 0 T)) :
    Tendsto (dyadicTimeLeftSum g T) atTop (𝓝 (∫ r in (0 : ℝ)..T.val, g r.toNNReal)) := by
  let G : ℝ → ℝ := fun r => g (min r.toNNReal T)
  have hc : Continuous G := hg.comp_continuous (by fun_prop) (fun r => ⟨zero_le, min_le_right _ _⟩)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hb : ∀ r, |G r| ≤ M := fun r => hM _ ⟨zero_le, min_le_right _ _⟩
  have hG (t : ℝ≥0) (ht : t ≤ T) : G t.val = g t := by
    calc
      _ = g (min t T) := congrArg (fun q : ℝ≥0 => g (min q T)) (Real.toNNReal_coe (r := t))
      _ = _ := congrArg g (min_eq_left ht)
  have ht := brownianItoDriftSum_bounded_continuous_tendsto
    (B := fun t : ℝ≥0 => fun _ : Unit => t.val) hc hb T () continuous_subtype_val
  have hs (n : ℕ) : brownianItoDriftSum (fun t : ℝ≥0 => fun _ : Unit => t.val) G T n () =
      dyadicTimeLeftSum g T n := by
    unfold brownianItoDriftSum dyadicTimeLeftSum
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z : ℝ => ((brownianDyadicGrid T n i.succ).val -
      (brownianDyadicGrid T n i.castSucc).val) * z)
      (hG _ (brownianDyadicGrid_mem_Icc T n i.castSucc).2)
  have hi : brownianItoDrift (fun t : ℝ≥0 => fun _ : Unit => t.val) G T () =
      ∫ r in (0 : ℝ)..T.val, g r.toNNReal := by
    unfold brownianItoDrift
    apply intervalIntegral.integral_congr
    intro r hr
    have hrT : r.toNNReal ≤ T := by
      apply Real.toNNReal_le_iff_le_coe.mpr
      exact hr.2.trans (max_le T.coe_nonneg le_rfl)
    exact hG _ hrT
  simpa only [hs, hi] using ht

theorem dyadicCoarseWeight_approximation (g : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (hg : ContinuousOn g (Icc 0 T)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ n),
      |g (brownianDyadicGrid T n i.castSucc) -
        dyadicCoarseWeight g T m (brownianDyadicGrid T n i.succ)| ≤ η := by
  have hmesh : Tendsto (fun n : ℕ => T.val / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul T.val
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) η hη
  have hhalf : 0 < δ / 2 := half_pos hδ
  filter_upwards [hmesh.eventually (gt_mem_nhds hhalf)] with m hm
  filter_upwards [hmesh.eventually (gt_mem_nhds hhalf)] with n hn i
  have hrpos : 0 < brownianDyadicGrid T n i.succ := by
    unfold brownianDyadicGrid
    simp only [Fin.val_succ]
    positivity
  obtain ⟨j, hj⟩ := brownianDyadicGrid_cell T m
    (show (brownianDyadicGrid T n i.succ).val ∈ Ioc 0 T.val from
      ⟨hrpos, (brownianDyadicGrid_mem_Icc T n i.succ).2⟩)
  have hd1 : dist (brownianDyadicGrid T n i.castSucc) (brownianDyadicGrid T n i.succ) =
      T.val / (2 : ℝ) ^ n := by
    change |(brownianDyadicGrid T n i.castSucc).val - (brownianDyadicGrid T n i.succ).val| = _
    rw [abs_sub_comm, brownianDyadicGrid_gap]
  have hd2 : dist (brownianDyadicGrid T n i.succ) (brownianDyadicGrid T m j.castSucc) ≤
      T.val / (2 : ℝ) ^ m := by
    change |(brownianDyadicGrid T n i.succ).val - (brownianDyadicGrid T m j.castSucc).val| ≤ _
    rw [abs_of_nonneg (sub_nonneg.mpr hj.1.le)]
    calc
      _ ≤ (brownianDyadicGrid T m j.succ).val - (brownianDyadicGrid T m j.castSucc).val :=
        sub_le_sub_right hj.2 _
      _ ≤ |(brownianDyadicGrid T m j.succ).val - (brownianDyadicGrid T m j.castSucc).val| := le_abs_self _
      _ = _ := brownianDyadicGrid_gap T m j
  have hd : dist (brownianDyadicGrid T n i.castSucc) (brownianDyadicGrid T m j.castSucc) < δ := by
    have ht := dist_triangle (brownianDyadicGrid T n i.castSucc)
      (brownianDyadicGrid T n i.succ) (brownianDyadicGrid T m j.castSucc)
    rw [hd1] at ht
    linarith
  rw [dyadicCoarseWeight_cell g T m _ j hj]
  exact (hc _ (brownianDyadicGrid_mem_Icc T n i.castSucc)
    _ (brownianDyadicGrid_mem_Icc T m j.castSucc) hd).le

end TimeTraps.Probability
