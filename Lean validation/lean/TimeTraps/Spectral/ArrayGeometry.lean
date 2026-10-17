module

public import TimeTraps.Spectral.ArrayNormalization

@[expose] public section

/-! Exact reconstruction of cyclic gaps from physical sites, and of sites
from their normalized gap data. No symmetry assumption enters admissibility. -/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem CircleProblem.gap_between_sites (C : CircleProblem (n + 1)) (i : Fin n) :
    C.gap i.castSucc = C.site i.succ - C.site i.castSucc := by
  have h := C.boundary_succ i.castSucc
  change C.site i.succ = C.site i.castSucc + C.gap i.castSucc at h
  linarith

theorem CircleProblem.gap_after_last_site (C : CircleProblem (n + 1)) :
    C.gap (Fin.last n) = C.length - C.site (Fin.last n) := by
  have h := C.boundary_succ (Fin.last n)
  change C.boundary (Fin.last (n + 1)) = C.site (Fin.last n) + C.gap (Fin.last n) at h
  rw [C.boundary_last] at h
  linarith

theorem PeriodicArray.gaps_eq_of_relative_sites (P : PeriodicArray n) (C : CircleProblem n)
    (hL : P.length = C.length) (hs : ∀ i, P.site i - P.offset = C.site i) : P.gap = C.gap := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ P.count_pos)
  | succ n =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [P.gap_last, C.gap_after_last_site, hL]
      linarith [hs (Fin.last n)]
    · rw [P.gap_castSucc, C.gap_between_sites]
      linarith [hs j.succ, hs j.castSucc]

def PlacementProblem.AdmissibleArray (C : PlacementProblem n) (x : Fin n → ℝ) : Prop :=
  StrictMono x ∧ ∀ i, x i ∈ Ico 0 C.length

def PlacementProblem.array (C : PlacementProblem n) (x : Fin n → ℝ) (hx : C.AdmissibleArray x) :
    PeriodicArray n where
  count_pos := C.count_pos
  length := C.length
  length_pos := C.length_pos
  diffusivity := C.diffusivity
  diffusivity_pos := C.diffusivity_pos
  site := x
  site_strictMono := hx.1
  site_mem := hx.2
  strength := C.strength
  strength_pos := C.strength_pos

theorem PlacementProblem.array_prescribed (C : PlacementProblem n) (x : Fin n → ℝ)
    (hx : C.AdmissibleArray x) : (C.array x hx).normalized.prescribed = C := rfl

theorem PlacementProblem.array_normalized (C : PlacementProblem n) (x : Fin n → ℝ)
    (hx : C.AdmissibleArray x) :
    (C.array x hx).normalized = C.circle (C.array x hx).gap
      ⟨(C.array x hx).gap_pos, (C.array x hx).gap_sum⟩ := rfl

theorem PlacementProblem.array_optimal_gap_iff (C : PlacementProblem n) (x : Fin n → ℝ)
    (hx : C.AdmissibleArray x) : (C.array x hx).gap = C.optimalCircleGap ↔
      ∀ i, x i = (C.array x hx).offset + C.optimalCircle.site i := by
  constructor
  · intro hg i
    have hi := (C.array x hx).normalized_site i
    change TimeTraps.Interval.absorptionPrefix (C.array x hx).gap i.castSucc =
      x i - (C.array x hx).offset at hi
    rw [hg] at hi
    change C.optimalCircle.site i = x i - (C.array x hx).offset at hi
    linarith
  · intro hs
    apply (C.array x hx).gaps_eq_of_relative_sites C.optimalCircle rfl
    intro i
    change x i - (C.array x hx).offset = C.optimalCircle.site i
    linarith [hs i]

theorem PlacementProblem.optimalCircle_sites_admissible (C : PlacementProblem n) :
    C.AdmissibleArray C.optimalCircle.site :=
  ⟨C.optimalCircle.site_strictMono, C.optimalCircle.site_mem⟩

theorem PlacementProblem.optimal_array_offset (C : PlacementProblem n) :
    (C.array C.optimalCircle.site C.optimalCircle_sites_admissible).offset = 0 := C.optimalCircle.site_zero

theorem PlacementProblem.optimal_array_gaps (C : PlacementProblem n) :
    (C.array C.optimalCircle.site C.optimalCircle_sites_admissible).gap = C.optimalCircleGap := by
  apply (C.array_optimal_gap_iff _ C.optimalCircle_sites_admissible).mpr
  intro i
  rw [C.optimal_array_offset, zero_add]

end TimeTraps.Spectral
