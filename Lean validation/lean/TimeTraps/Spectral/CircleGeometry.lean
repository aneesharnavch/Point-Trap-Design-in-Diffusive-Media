module

public import TimeTraps.Spectral.NetworkProblem
public import TimeTraps.Interval.AbsorptionCDF
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-! Cyclic arc data and ordered physical coordinates with a wrap edge. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Graph TimeTraps.Interval
open scoped BigOperators

theorem cyclic_incidence_connected (n : ℕ) :
    IncidenceConnected (fun i : Fin n => i) (finRotate n) := by
  cases n with
  | zero => intro v; exact Fin.elim0 v
  | succ n =>
    have hp : ∀ v : Fin (n + 1),
        Relation.EqvGen (fun v w => ∃ i : Fin (n + 1), i = v ∧ finRotate (n + 1) i = w) 0 v := by
      intro v
      induction v using Fin.induction with
      | zero => exact Relation.EqvGen.refl 0
      | succ i ih =>
        apply Relation.EqvGen.trans _ _ _ ih
        apply Relation.EqvGen.rel
        exact ⟨i.castSucc, rfl, finRotate_of_lt i.isLt⟩
    intro v w
    exact Relation.EqvGen.trans v 0 w (Relation.EqvGen.symm 0 v (hp v)) (hp w)

structure CircleProblem (n : ℕ) where
  count_pos : 0 < n
  length : ℝ
  length_pos : 0 < length
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  gap : Fin n → ℝ
  gap_pos : ∀ i, 0 < gap i
  gap_sum : (∑ i, gap i) = length
  strength : Fin n → ℝ
  strength_pos : ∀ i, 0 < strength i

variable {n : ℕ}

def CircleProblem.network (C : CircleProblem n) : SpectralNetwork (Fin n) (Fin n) where
  tail := fun i => i
  head := finRotate n
  length := C.gap
  length_pos := C.gap_pos
  diffusivity := C.diffusivity
  diffusivity_pos := C.diffusivity_pos
  strength := C.strength
  strength_pos := C.strength_pos
  connected := cyclic_incidence_connected n

noncomputable def CircleProblem.boundary (C : CircleProblem n) : Fin (n + 1) → ℝ :=
  absorptionPrefix C.gap

noncomputable def CircleProblem.site (C : CircleProblem n) (i : Fin n) : ℝ :=
  C.boundary i.castSucc

theorem CircleProblem.network_totalLength (C : CircleProblem n) :
    C.network.totalLength = C.length := C.gap_sum

theorem CircleProblem.boundary_zero (C : CircleProblem n) : C.boundary 0 = 0 :=
  absorptionPrefix_zero C.gap

theorem CircleProblem.boundary_last (C : CircleProblem n) : C.boundary (Fin.last n) = C.length := by
  rw [boundary, absorptionPrefix_last, C.gap_sum]

theorem CircleProblem.boundary_succ (C : CircleProblem n) (i : Fin n) :
    C.boundary i.succ = C.site i + C.gap i := absorptionPrefix_succ C.gap i

theorem CircleProblem.boundary_strictMono (C : CircleProblem n) : StrictMono C.boundary :=
  absorptionPrefix_strictMono C.gap C.gap_pos

theorem CircleProblem.site_strictMono (C : CircleProblem n) : StrictMono C.site :=
  fun _ _ h => C.boundary_strictMono h

theorem CircleProblem.site_mem (C : CircleProblem n) (i : Fin n) : C.site i ∈ Ico 0 C.length := by
  constructor
  · have h := C.boundary_strictMono.monotone (Fin.zero_le i.castSucc)
    simpa only [site, C.boundary_zero] using h
  · have h := C.boundary_strictMono (Fin.castSucc_lt_last i)
    simpa only [site, C.boundary_last] using h

theorem CircleProblem.site_zero (C : CircleProblem n) : C.site ⟨0, C.count_pos⟩ = 0 :=
  C.boundary_zero

theorem CircleProblem.wrap_trace (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy C.network.geometry U u) :
    u (Fin.last n) (C.gap (Fin.last n)) = u 0 0 := by
  have ht := hu.tail_value 0
  have hh := hu.head_value (Fin.last n)
  change u 0 0 = U 0 at ht
  change u (Fin.last n) (C.gap (Fin.last n)) = U (finRotate (n + 1) (Fin.last n)) at hh
  rw [finRotate_last] at hh
  exact hh.trans ht.symm

end TimeTraps.Spectral
