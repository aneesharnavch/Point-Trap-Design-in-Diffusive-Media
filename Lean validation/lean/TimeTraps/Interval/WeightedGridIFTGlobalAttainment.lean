module

public import TimeTraps.Interval.WeightedGridIFTGlobal

@[expose] public section

/-! Positive affine weights and attainment by the implicit-function branch
follow from compact bounds, without an assumed positive perturbation family. -/

namespace TimeTraps.Interval

open Set Filter
open scoped Topology ContDiff

variable {n : ℕ}

theorem gridIFT_affine_positive (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, |ε| < η →
      ∀ z ∈ Icc (0 : ℝ) 1, 0 < Ω * (1 + ε * h z) := by
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0 ⟨le_rfl, zero_le_one⟩)
  have hp : 0 < H + 1 := by linarith
  refine ⟨1 / (H + 1), div_pos zero_lt_one hp, ?_⟩
  intro ε hε z hz
  have he := (lt_div_iff₀ hp).mp hε
  have hhz : |h z| ≤ H := by simpa only [Real.norm_eq_abs] using hH z hz
  have hab : |ε * h z| < 1 := by
    rw [abs_mul]
    have hm := mul_le_mul_of_nonneg_left hhz (abs_nonneg ε)
    nlinarith [abs_nonneg ε]
  exact mul_pos hΩ (by linarith [(neg_abs_le (ε * h z)), hab])

theorem gridIFT_affine_weight_exists (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, |ε| < η → ∃ W : CellWeight,
      ∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω * (1 + ε * h z) := by
  obtain ⟨η, hη, hp⟩ := gridIFT_affine_positive h hh Ω hΩ
  refine ⟨η, hη, ?_⟩
  intro ε hε
  exact ⟨⟨fun z => Ω * (1 + ε * h z),
    continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul hh)), hp ε hε⟩,
    fun _ _ => rfl⟩

theorem gridIFTBranch_minimizer_iff (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, |ε| < η → ∀ W : CellWeight,
      (∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω * (1 + ε * h z)) →
      ∀ Q : ClosedPartition (n + 1),
      (∀ P : ClosedPartition (n + 1), Q.gridCost W ≤ P.gridCost W) ↔
        Q.point = cdfNode (gridIFTBranch h hh Ω hΩ ε) := by
  obtain ⟨η, hη, hall⟩ := gridIFTBranch_all_minimizers (n := n) h hh Ω hΩ
  refine ⟨η, hη, ?_⟩
  intro ε hε W hW Q
  constructor
  · intro hQ
    exact Q.gridIFTCoordinates_nodes.symm.trans (congrArg cdfNode (hall ε hε W hW Q hQ))
  · intro hQ
    obtain ⟨P, hP⟩ := ClosedPartition.grid_minimum_exists W (Nat.succ_pos n)
    have hpoint : P.point = cdfNode (gridIFTBranch h hh Ω hΩ ε) :=
      P.gridIFTCoordinates_nodes.symm.trans (congrArg cdfNode (hall ε hε W hW P hP))
    have he : Q = P := Subtype.ext (hQ.trans hpoint.symm)
    exact he ▸ hP

theorem gridIFTBranch_strict_attainment (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, |ε| < η →
      StrictMono (cdfNode (gridIFTBranch (n := n) h hh Ω hΩ ε)) ∧
      ∃ W : CellWeight,
        (∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω * (1 + ε * h z)) ∧
        ∃ Q : StrictPartition (n + 1),
          Q.point = cdfNode (gridIFTBranch h hh Ω hΩ ε) ∧
          ∀ P : ClosedPartition (n + 1),
            (∀ R : ClosedPartition (n + 1), P.gridCost W ≤ R.gridCost W) ↔ P = Q.closed := by
  obtain ⟨η, hη, hall⟩ := gridIFTBranch_minimizer_iff (n := n) h hh Ω hΩ
  obtain ⟨δ, hδ, hex⟩ := gridIFT_affine_weight_exists h hh.continuousOn Ω hΩ
  refine ⟨min η δ, lt_min hη hδ, ?_⟩
  intro ε hε
  obtain ⟨W, hW⟩ := hex ε (lt_of_lt_of_le hε (min_le_right η δ))
  obtain ⟨Q, hQ⟩ := StrictPartition.grid_minimum_exists W (Nat.succ_pos n)
  have he := (hall ε (lt_of_lt_of_le hε (min_le_left η δ)) W hW Q.closed).mp hQ
  change Q.point = cdfNode (gridIFTBranch h hh Ω hΩ ε) at he
  refine ⟨he ▸ Q.strictMono, W, hW, Q, he, ?_⟩
  intro P
  rw [hall ε (lt_of_lt_of_le hε (min_le_left η δ)) W hW P, ← he]
  constructor
  · exact fun hp => Subtype.ext hp
  · intro hp
    exact congrArg ClosedPartition.point hp

end TimeTraps.Interval
