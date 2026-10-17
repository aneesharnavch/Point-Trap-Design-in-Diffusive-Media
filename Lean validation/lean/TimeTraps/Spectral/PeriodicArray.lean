module

public import TimeTraps.Spectral.CirclePhysicalOptimality

@[expose] public section

/-! An arbitrary sorted physical trap array on [0,L), independently of a
choice of cut at a trap. Cyclic gaps include the wrap from the last trap. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval
open scoped BigOperators

structure PeriodicArray (n : ℕ) where
  count_pos : 0 < n
  length : ℝ
  length_pos : 0 < length
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  site : Fin n → ℝ
  site_strictMono : StrictMono site
  site_mem : ∀ i, site i ∈ Ico 0 length
  strength : Fin n → ℝ
  strength_pos : ∀ i, 0 < strength i

variable {n : ℕ}

def PeriodicArray.first (P : PeriodicArray n) : Fin n := ⟨0, P.count_pos⟩

noncomputable def PeriodicArray.offset (P : PeriodicArray n) : ℝ := P.site P.first

theorem PeriodicArray.offset_mem (P : PeriodicArray n) : P.offset ∈ Ico 0 P.length := P.site_mem P.first

theorem PeriodicArray.offset_le_site (P : PeriodicArray n) (i : Fin n) : P.offset ≤ P.site i :=
  P.site_strictMono.monotone (show P.first ≤ i from Nat.zero_le i.val)

noncomputable def PeriodicArray.gap (P : PeriodicArray n) (i : Fin n) : ℝ :=
  if h : i.val + 1 < n then P.site ⟨i.val + 1, h⟩ - P.site i
  else P.length + P.offset - P.site i

theorem PeriodicArray.gap_castSucc (P : PeriodicArray (n + 1)) (i : Fin n) :
    P.gap i.castSucc = P.site i.succ - P.site i.castSucc := by
  rw [gap, dif_pos (show i.castSucc.val + 1 < n + 1 from Nat.succ_lt_succ i.isLt)]
  rfl

theorem PeriodicArray.gap_last (P : PeriodicArray (n + 1)) :
    P.gap (Fin.last n) = P.length + P.offset - P.site (Fin.last n) := by
  rw [gap, dif_neg (show ¬ ((Fin.last n).val + 1 < n + 1) by simp)]

theorem PeriodicArray.gap_pos (P : PeriodicArray n) (i : Fin n) : 0 < P.gap i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [P.gap_last]
      linarith [(P.site_mem (Fin.last n)).2, P.offset_mem.1]
    · rw [P.gap_castSucc]
      exact sub_pos.mpr (P.site_strictMono Fin.castSucc_lt_succ)

theorem PeriodicArray.gap_sum (P : PeriodicArray n) : (∑ i, P.gap i) = P.length := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ P.count_pos)
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    simp_rw [P.gap_castSucc]
    rw [P.gap_last]
    have hs : (∑ i : Fin n, (P.site i.succ - P.site i.castSucc)) =
        P.site (Fin.last n) - P.site 0 := by
      rw [Finset.sum_sub_distrib]
      have ha := Fin.sum_univ_succ P.site
      have hb := Fin.sum_univ_castSucc P.site
      linarith
    rw [hs]
    change P.site (Fin.last n) - P.site 0 + (P.length + P.site 0 - P.site (Fin.last n)) = P.length
    ring

noncomputable def PeriodicArray.normalized (P : PeriodicArray n) : CircleProblem n where
  count_pos := P.count_pos
  length := P.length
  length_pos := P.length_pos
  diffusivity := P.diffusivity
  diffusivity_pos := P.diffusivity_pos
  gap := P.gap
  gap_pos := P.gap_pos
  gap_sum := P.gap_sum
  strength := P.strength
  strength_pos := P.strength_pos

theorem PeriodicArray.normalized_site (P : PeriodicArray n) (i : Fin n) :
    P.normalized.site i = P.site i - P.offset := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction i using Fin.induction with
    | zero =>
      have hz : P.normalized.site (0 : Fin (n + 1)) = 0 := P.normalized.site_zero
      rw [hz]
      change (0 : ℝ) = P.site 0 - P.site 0
      ring
    | succ j ih =>
      have h := P.normalized.boundary_succ j.castSucc
      change P.normalized.site j.succ = P.normalized.site j.castSucc + P.gap j.castSucc at h
      rw [h, ih, P.gap_castSucc]
      ring

theorem PeriodicArray.normalized_site_mem (P : PeriodicArray n) (i : Fin n) :
    P.normalized.site i ∈ Ico 0 (P.length - P.offset) := by
  rw [P.normalized_site]
  exact ⟨sub_nonneg.mpr (P.offset_le_site i), sub_lt_sub_right (P.site_mem i).2 _⟩

def PeriodicArray.Energy (P : PeriodicArray n) (u : ℝ → ℝ) : Prop :=
  IntervalEnergy u 0 P.length ∧ u 0 = u P.length

noncomputable def PeriodicArray.quadraticForm (P : PeriodicArray n) (u : ℝ → ℝ) : ℝ :=
  P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x ^ 2) + ∑ i, P.strength i * u (P.site i) ^ 2

noncomputable def PeriodicArray.squareMass (P : PeriodicArray n) (u : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..P.length, u x ^ 2

def PeriodicArray.rayleighValues (P : PeriodicArray n) : Set ℝ :=
  {r | ∃ u : ℝ → ℝ, P.Energy u ∧ 0 < P.squareMass u ∧ r = P.quadraticForm u / P.squareMass u}

noncomputable def PeriodicArray.principalValue (P : PeriodicArray n) : ℝ := sInf P.rayleighValues

end TimeTraps.Spectral
