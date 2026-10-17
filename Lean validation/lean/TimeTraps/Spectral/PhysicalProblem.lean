module

public import TimeTraps.Spectral.Shooting
public import TimeTraps.Interval.HomogeneousMedium
public import TimeTraps.Interval.PiecewiseEnergy

@[expose] public section

/-!
Independent physical spectral data: interval length, diffusion constant,
ordered interior sites and positive strengths. The associated gap lengths
and normalized derivative jumps are derived from those inputs.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph
open scoped BigOperators

structure SpectralProblem (n : ℕ) where
  count_pos : 0 < n
  length : ℝ
  length_pos : 0 < length
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  site : Fin n → ℝ
  site_strictMono : StrictMono site
  site_interior : ∀ i, site i ∈ Ioo (0 : ℝ) length
  strength : Fin n → ℝ
  strength_pos : ∀ i, 0 < strength i

variable {n : ℕ}

def SpectralProblem.geometry (P : SpectralProblem n) : OrderedMedium n :=
  OrderedMedium.ofSites
    (homogeneous P.length P.diffusivity P.length_pos P.diffusivity_pos).source
    (fun _ => P.diffusivity) continuousOn_const (fun _ _ => P.diffusivity_pos)
    P.site P.site_strictMono P.site_interior

theorem SpectralProblem.geometry_site (P : SpectralProblem n) (i : Fin n) : P.geometry.site i = P.site i :=
  OrderedMedium.ofSites_site _ _ _ _ _ _ _ i

theorem SpectralProblem.geometry_left (P : SpectralProblem n) : P.geometry.source.left = 0 := rfl

theorem SpectralProblem.geometry_right (P : SpectralProblem n) : P.geometry.source.right = P.length := rfl

noncomputable def SpectralProblem.shooting (P : SpectralProblem n) : ShootingData n where
  gap := P.geometry.gapLength
  gap_pos := P.geometry.gapLength_pos
  reaction := fun i => P.strength i / P.diffusivity
  reaction_pos := fun i => div_pos (P.strength_pos i) P.diffusivity_pos

theorem SpectralProblem.shooting_gap (P : SpectralProblem n) (e : Fin (n + 1)) :
    P.shooting.gap e = P.geometry.node e.succ - P.geometry.node e.castSucc := rfl

theorem SpectralProblem.shooting_reaction (P : SpectralProblem n) (i : Fin n) :
    P.shooting.reaction i = P.strength i / P.diffusivity := rfl

noncomputable def SpectralProblem.quadraticForm (P : SpectralProblem n) (v : ℝ → ℝ) : ℝ :=
  P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv v x ^ 2) +
    ∑ i, P.strength i * v (P.site i) ^ 2

noncomputable def SpectralProblem.squareMass (P : SpectralProblem n) (v : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..P.length, v x ^ 2

def SpectralProblem.rayleighValues (P : SpectralProblem n) : Set ℝ :=
  {r | ∃ v : ℝ → ℝ, IntervalEnergy v 0 P.length ∧ 0 < P.squareMass v ∧
    r = P.quadraticForm v / P.squareMass v}

/-- The principal variational value is defined before any shooting root is
identified with it. Its competitors are all nonzero physical H1 functions. -/
noncomputable def SpectralProblem.principalValue (P : SpectralProblem n) : ℝ := sInf P.rayleighValues

theorem SpectralProblem.quadraticForm_nonneg (P : SpectralProblem n) (v : ℝ → ℝ) :
    0 ≤ P.quadraticForm v := by
  apply add_nonneg
  · exact mul_nonneg P.diffusivity_pos.le
      (intervalIntegral.integral_nonneg P.length_pos.le (fun x _ => sq_nonneg (deriv v x)))
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (P.strength_pos i).le (sq_nonneg _))

theorem SpectralProblem.squareMass_one (P : SpectralProblem n) : P.squareMass (fun _ => 1) = P.length := by
  simp [squareMass]

theorem SpectralProblem.rayleighValues_nonempty (P : SpectralProblem n) : P.rayleighValues.Nonempty := by
  refine ⟨P.quadraticForm (fun _ => 1) / P.squareMass (fun _ => 1),
    (fun _ => 1), IntervalEnergy.const 1 0 P.length, ?_, rfl⟩
  rw [P.squareMass_one]
  exact P.length_pos

theorem SpectralProblem.rayleighValues_bddBelow (P : SpectralProblem n) : BddBelow P.rayleighValues := by
  refine ⟨0, ?_⟩
  rintro r ⟨v, _, hv, rfl⟩
  exact div_nonneg (P.quadraticForm_nonneg v) hv.le

theorem SpectralProblem.principalValue_nonneg (P : SpectralProblem n) : 0 ≤ P.principalValue := by
  apply le_csInf P.rayleighValues_nonempty
  rintro r ⟨v, _, hv, rfl⟩
  exact div_nonneg (P.quadraticForm_nonneg v) hv.le

end TimeTraps.Spectral
