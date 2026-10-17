module

public import TimeTraps.Interval.CellPerturbation
public import TimeTraps.Interval.CellSplitting
public import TimeTraps.Interval.ConstantCell

@[expose] public section

/-!
The three source-coordinate cell barriers for a mixed endpoint architecture.
A left-endpoint trap is at the left end of its cell, so its barrier is the
right rise; a right-endpoint trap uses the left rise. Physical endpoint
cells specialize these formulas to α = 0 or β = 1. Subcell comparisons keep
the cell kind fixed and make no assertion across different orientations.
-/

namespace TimeTraps.Interval

open Set MeasureTheory

inductive CellKind where
  | ordinary
  | leftEndpoint
  | rightEndpoint
  deriving DecidableEq

noncomputable def CellWeight.orientedBarrier (W : CellWeight) (kind : CellKind)
    (α β : ℝ) : ℝ :=
  match kind with
  | .ordinary => W.barrier α β
  | .leftEndpoint => W.rightRise β α
  | .rightEndpoint => W.leftRise α β

theorem CellWeight.orientedBarrier_ordinary_integral (W : CellWeight) (α β : ℝ) :
    W.orientedBarrier .ordinary α β =
      ∫ s in α..W.center α β, W.value s * (s - α) := rfl

theorem CellWeight.orientedBarrier_leftEndpoint_integral (W : CellWeight) (α β : ℝ) :
    W.orientedBarrier .leftEndpoint α β =
      ∫ s in α..β, W.value s * (β - s) := rfl

theorem CellWeight.orientedBarrier_rightEndpoint_integral (W : CellWeight) (α β : ℝ) :
    W.orientedBarrier .rightEndpoint α β =
      ∫ s in α..β, W.value s * (s - α) := rfl

theorem CellWeight.orientedBarrier_ordinary_right_integral (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.orientedBarrier .ordinary α β =
      ∫ s in W.center α β..β, W.value s * (β - s) := by
  change W.leftRise α (W.center α β) = W.rightRise β (W.center α β)
  rcases hab.lt_or_eq with hlt | rfl
  · exact (W.center_spec hα hβ hlt).2
  · rw [W.center_diagonal, W.leftRise_self, W.rightRise_self]

theorem CellWeight.orientedBarrier_diagonal (W : CellWeight) (kind : CellKind) (α : ℝ) :
    W.orientedBarrier kind α α = 0 := by
  cases kind <;> simp only [orientedBarrier, W.barrier_diagonal, W.leftRise_self,
    W.rightRise_self]

theorem CellWeight.orientedBarrier_pos (W : CellWeight) (kind : CellKind) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) :
    0 < W.orientedBarrier kind α β := by
  cases kind with
  | ordinary => exact W.barrier_pos hα hβ hab
  | leftEndpoint => exact W.rightRise_pos hα hβ hab
  | rightEndpoint => exact W.leftRise_pos hα hβ hab

theorem CellWeight.orientedBarrier_nonneg (W : CellWeight) (kind : CellKind) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    0 ≤ W.orientedBarrier kind α β := by
  rcases hab.lt_or_eq with hlt | rfl
  · exact (W.orientedBarrier_pos kind hα hβ hlt).le
  · rw [W.orientedBarrier_diagonal]

theorem CellWeight.orientedBarrier_zero_iff (W : CellWeight) (kind : CellKind) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.orientedBarrier kind α β = 0 ↔ α = β := by
  constructor
  · intro hz
    rcases hab.lt_or_eq with hlt | he
    · exact False.elim ((ne_of_gt (W.orientedBarrier_pos kind hα hβ hlt)) hz)
    · exact he
  · rintro rfl
    exact W.orientedBarrier_diagonal kind α

theorem CellWeight.orientedBarrier_continuous (W : CellWeight) (kind : CellKind) :
    ContinuousOn (fun p : ℝ × ℝ => W.orientedBarrier kind p.1 p.2) cellDomain := by
  cases kind with
  | ordinary => exact W.barrier_continuous
  | leftEndpoint =>
      exact W.rightRise_joint_continuous continuous_snd.continuousOn continuous_fst.continuousOn
        (fun _ hp => cell_right_mem hp) (fun _ hp => cell_left_mem hp)
  | rightEndpoint =>
      exact W.leftRise_joint_continuous continuous_fst.continuousOn continuous_snd.continuousOn
        (fun _ hp => cell_left_mem hp) (fun _ hp => cell_right_mem hp)

theorem CellWeight.orientedBarrier_subcell_le (W : CellWeight) (kind : CellKind)
    {α γ δ β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1)
    (hag : α ≤ γ) (hgd : γ ≤ δ) (hdb : δ ≤ β) :
    W.orientedBarrier kind γ δ ≤ W.orientedBarrier kind α β := by
  have hab : α ≤ β := hag.trans (hgd.trans hdb)
  cases kind with
  | ordinary => exact W.barrier_subcell_le hα hβ hag hgd hdb
  | leftEndpoint =>
      change W.rightRise δ γ ≤ W.rightRise β α
      have he : W.rightRise δ γ ≤ W.rightRise β γ := by
        rcases hdb.lt_or_eq with hlt | rfl
        · exact (W.rightRise_strict_endpoint (hα.trans hag) hβ hgd hlt).le
        · exact le_rfl
      exact he.trans ((W.rightRise_strictAnti hα hβ hab).antitoneOn
        ⟨le_rfl, hab⟩ ⟨hag, hgd.trans hdb⟩ hag)
  | rightEndpoint =>
      change W.leftRise γ δ ≤ W.leftRise α β
      have he : W.leftRise γ δ ≤ W.leftRise α δ := by
        rcases hag.lt_or_eq with hlt | rfl
        · exact (W.leftRise_strict_endpoint hα (hdb.trans hβ) hlt hgd).le
        · exact le_rfl
      exact he.trans ((W.leftRise_strictMono hα hβ hab).monotoneOn
        ⟨hag.trans hgd, hdb⟩ ⟨hab, le_rfl⟩ hdb)

theorem CellWeight.orientedBarrier_strict_subcell (W : CellWeight) (kind : CellKind)
    {α γ δ β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1)
    (hag : α ≤ γ) (hgd : γ < δ) (hdb : δ ≤ β)
    (hproper : α < γ ∨ δ < β) :
    W.orientedBarrier kind γ δ < W.orientedBarrier kind α β := by
  have hab : α ≤ β := hag.trans (hgd.le.trans hdb)
  cases kind with
  | ordinary => exact W.barrier_strict_subcell hα hβ hag hgd hdb hproper
  | leftEndpoint =>
      change W.rightRise δ γ < W.rightRise β α
      rcases hproper with hleft | hright
      · have he := W.orientedBarrier_subcell_le .leftEndpoint
          (hα.trans hag) hβ le_rfl hgd.le hdb
        exact he.trans_lt ((W.rightRise_strictAnti hα hβ hab)
          ⟨le_rfl, hab⟩ ⟨hag, hgd.le.trans hdb⟩ hleft)
      · have he := W.orientedBarrier_subcell_le .leftEndpoint
          hα hβ hag (hgd.le.trans hdb) le_rfl
        exact (W.rightRise_strict_endpoint (hα.trans hag) hβ hgd.le hright).trans_le he
  | rightEndpoint =>
      change W.leftRise γ δ < W.leftRise α β
      rcases hproper with hleft | hright
      · have he := W.orientedBarrier_subcell_le .rightEndpoint
          hα hβ le_rfl (hag.trans hgd.le) hdb
        exact (W.leftRise_strict_endpoint hα (hdb.trans hβ) hleft hgd.le).trans_le he
      · have he := W.orientedBarrier_subcell_le .rightEndpoint
          hα (hdb.trans hβ) hag hgd.le le_rfl
        exact he.trans_lt ((W.leftRise_strictMono hα hβ hab)
          ⟨hag.trans hgd.le, hdb⟩ ⟨hab, le_rfl⟩ hright)

theorem CellWeight.orientedBarrier_constant (W : CellWeight) (kind : CellKind) {C α β : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C)
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.orientedBarrier kind α β =
      match kind with
      | .ordinary => C * (β - α) ^ 2 / 8
      | .leftEndpoint => C * (β - α) ^ 2 / 2
      | .rightEndpoint => C * (β - α) ^ 2 / 2 := by
  cases kind with
  | ordinary => exact W.barrier_constant hC hα hβ hab
  | leftEndpoint => exact W.rightRise_constant hC hα hβ hab
  | rightEndpoint => exact W.leftRise_constant hC hα hβ hab

theorem CellWeight.orientedBarrier_mono_weight (W V : CellWeight) (kind : CellKind)
    (hWV : ∀ z ∈ Icc (0 : ℝ) 1, W.value z ≤ V.value z)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.orientedBarrier kind α β ≤ V.orientedBarrier kind α β := by
  cases kind with
  | ordinary => exact W.barrier_mono_weight V hWV hα hβ hab
  | leftEndpoint => exact W.rightRise_mono_weight V hWV hα hβ hab
  | rightEndpoint => exact W.leftRise_mono_weight V hWV hα hβ hab

theorem CellWeight.orientedBarrier_lt_weight (W V : CellWeight) (kind : CellKind)
    (hWV : ∀ z ∈ Icc (0 : ℝ) 1, W.value z < V.value z)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) :
    W.orientedBarrier kind α β < V.orientedBarrier kind α β := by
  cases kind with
  | ordinary => exact W.barrier_lt_weight V hWV hα hβ hab
  | leftEndpoint => exact W.rightRise_lt_weight V hWV hα hβ hab
  | rightEndpoint => exact W.leftRise_lt_weight V hWV hα hβ hab

theorem CellWeight.orientedBarrier_le_add_weight (W V : CellWeight) (kind : CellKind)
    {ε α β : ℝ} (hε : 0 ≤ ε)
    (hWV : ∀ z ∈ Icc (0 : ℝ) 1, W.value z ≤ V.value z + ε)
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.orientedBarrier kind α β ≤
      V.orientedBarrier kind α β + ε * (β - α) ^ 2 / 2 := by
  cases kind with
  | ordinary => exact W.barrier_le_add_weight V hε hWV hα hβ hab
  | leftEndpoint => exact W.rightRise_le_add_weight V hWV hα hβ hab
  | rightEndpoint => exact W.leftRise_le_add_weight V hWV hα hβ hab

theorem CellWeight.orientedBarrier_abs_sub_le (W V : CellWeight) (kind : CellKind)
    {ε α β : ℝ} (hWV : ∀ z ∈ Icc (0 : ℝ) 1, |W.value z - V.value z| ≤ ε)
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    |W.orientedBarrier kind α β - V.orientedBarrier kind α β| ≤ ε * (β - α) ^ 2 / 2 := by
  cases kind with
  | ordinary => exact W.barrier_abs_sub_le V hWV hα hβ hab
  | leftEndpoint => exact W.rightRise_abs_sub_le V hWV hα hβ hab
  | rightEndpoint => exact W.leftRise_abs_sub_le V hWV hα hβ hab

end TimeTraps.Interval
