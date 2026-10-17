module

public import TimeTraps.Interval.WeightedGridIFTValueBounds

@[expose] public section

/-! The independently defined perturbed objective evaluated on the branch,
and the quadratic envelope expansion for every attained global minimum. -/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped Topology ContDiff

variable {n : ℕ}

noncomputable def gridIFTValueCoefficient (h : ℝ → ℝ) (Ω : ℝ) (n : ℕ) : ℝ :=
  Ω * ∫ z in (0 : ℝ)..1, h z * gridDistance (cdfNode (gridIFTBaseline n)) z ^ 2

theorem gridIFT_minimum_value_expansion (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ W : CellWeight,
      (∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω * (1 + ε * h z)) →
      ∀ Q : ClosedPartition (n + 1),
      (∀ P : ClosedPartition (n + 1), Q.gridCost W ≤ P.gridCost W) →
      |Q.gridCost W - Ω / (12 * ((n : ℝ) + 1) ^ 2) -
        ε * gridIFTValueCoefficient h Ω n| ≤ C * ε ^ 2 := by
  obtain ⟨η, hη, hall⟩ := gridIFTBranch_minimizer_iff (n := n) h hh Ω hΩ
  obtain ⟨M, δ, hM, hδ, hlip⟩ := gridIFTBranch_nodes_lipschitz (n := n) h hh Ω hΩ
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hh.continuousOn
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0 ⟨le_rfl, zero_le_one⟩)
  let V : CellWeight := ⟨fun _ => Ω, continuousOn_const, fun _ _ => hΩ⟩
  let R := (StrictPartition.uniform (n + 1) (Nat.succ_pos n)).closed
  have hR : ∀ P : ClosedPartition (n + 1), R.gridCost V ≤ P.gridCost V := by
    intro P
    rw [StrictPartition.uniform_gridCost_constant V (Nat.succ_pos n) hΩ (fun _ _ => rfl)]
    exact P.constant_grid_lower V hΩ.le (fun _ _ => rfl)
  have hcost : R.gridCost V = Ω / (12 * ((n : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
      StrictPartition.uniform_gridCost_constant V (Nat.succ_pos n) hΩ (fun _ _ => rfl)
  have hcoef : Ω * R.gridSignedCost h = gridIFTValueCoefficient h Ω n := by
    unfold ClosedPartition.gridSignedCost gridIFTValueCoefficient
    rw [gridIFTBaseline_nodes]
    rfl
  refine ⟨2 * Ω * H * M + 1, min η δ, by positivity, lt_min hη hδ, ?_⟩
  intro ε hε W hW Q hQ
  have hnodes := (hall ε (lt_of_lt_of_le hε (min_le_left η δ)) W hW Q).mp hQ
  have hdist : ∀ v, |Q.point v - R.point v| ≤ M * |ε| := by
    intro v
    rw [hnodes]
    simpa only [R, ClosedPartition.point, StrictPartition.closed, StrictPartition.uniform,
      Nat.cast_add, Nat.cast_one] using
      hlip ε (lt_of_lt_of_le hε (min_le_right η δ)) v
  have hs := Q.gridSignedCost_perturbation R h hh.continuousOn
    (fun z hz => by simpa only [Real.norm_eq_abs] using hH z hz) hdist
  have hv := gridIFT_value_variational_bound Q R W V h Ω ε hΩ (fun _ _ => rfl) hW hQ hR
  rw [hcost, mul_assoc ε Ω, hcoef] at hv
  calc
    _ ≤ |ε| * Ω * |Q.gridSignedCost h - R.gridSignedCost h| := hv
    _ ≤ |ε| * Ω * (2 * H * (M * |ε|)) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (abs_nonneg ε) hΩ.le)
    _ = 2 * Ω * H * M * |ε| ^ 2 := by ring
    _ = 2 * Ω * H * M * ε ^ 2 := by rw [sq_abs]
    _ ≤ (2 * Ω * H * M + 1) * ε ^ 2 := by nlinarith [sq_nonneg ε]

noncomputable def gridIFTValue (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) (ε : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..1,
    Ω * (1 + ε * h z) * gridDistance (cdfNode (gridIFTBranch (n := n) h hh Ω hΩ ε)) z ^ 2

theorem gridIFTValue_eq_gridCost (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) (ε : ℝ)
    (W : CellWeight) (Q : ClosedPartition (n + 1))
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω * (1 + ε * h z))
    (hQ : Q.point = cdfNode (gridIFTBranch h hh Ω hΩ ε)) :
    gridIFTValue (n := n) h hh Ω hΩ ε = Q.gridCost W := by
  unfold gridIFTValue ClosedPartition.gridCost
  apply intervalIntegral.integral_congr
  intro z hz
  dsimp only
  rw [hW z (by simpa using hz), hQ]

theorem gridIFTValue_zero (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    gridIFTValue (n := n) h hh Ω hΩ 0 = Ω / (12 * ((n : ℝ) + 1) ^ 2) := by
  let V : CellWeight := ⟨fun _ => Ω, continuousOn_const, fun _ _ => hΩ⟩
  rw [gridIFTValue_eq_gridCost h hh Ω hΩ 0 V
    (StrictPartition.uniform (n + 1) (Nat.succ_pos n)).closed
    (by intro z _; simp [V])
    (by rw [gridIFTBranch_zero, gridIFTBaseline_nodes]; rfl)]
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
    StrictPartition.uniform_gridCost_constant V (Nat.succ_pos n) hΩ (fun _ _ => rfl)

theorem gridIFTValue_attained (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∃ W : CellWeight,
      (∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω * (1 + ε * h z)) ∧
      IsLeast (range (fun Q : ClosedPartition (n + 1) => Q.gridCost W))
        (gridIFTValue (n := n) h hh Ω hΩ ε) := by
  obtain ⟨δ, hδ, hatt⟩ := gridIFTBranch_strict_attainment (n := n) h hh Ω hΩ
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨_, W, hW, Q, hQ, hmin⟩ := hatt ε hε
  have he := gridIFTValue_eq_gridCost h hh Ω hΩ ε W Q.closed hW hQ
  refine ⟨W, hW, ?_⟩
  rw [he]
  refine ⟨⟨Q.closed, rfl⟩, ?_⟩
  rintro M ⟨P, rfl⟩
  exact (hmin Q.closed).mpr rfl P

end TimeTraps.Interval
