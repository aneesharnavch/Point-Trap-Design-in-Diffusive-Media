module

public import TimeTraps.Spectral.ReflectedEigenstateKinkBridge
public import TimeTraps.Spectral.IntervalOperatorBridge

@[expose] public section

/-! Every member of the actual complete operator eigenbasis has a global
C²-plus-finite-kinks representative on the physical interval. This is an
arbitrary eigenmode statement, with the original interior contacts and
reflecting endpoints; no ground-state positivity is used. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ} {P : SpectralProblem n} {ev : ℝ} {u : ℝ → ℝ}

theorem WeakEigenEquation.kink_representation (hu : WeakEigenEquation P ev u) :
    ∃ (F : ℝ → ℝ) (c : Fin n → ℝ), ContDiff ℝ 2 F ∧
      EqOn (finiteKinkPotential F Finset.univ P.site c) u (Icc 0 P.length) ∧
      (∀ z ∈ Icc 0 P.length, deriv (deriv F) z = -ev * u z / P.diffusivity) ∧
      finiteKinkSlope F Finset.univ P.site c 0 = 0 ∧
      finiteKinkSlope F Finset.univ P.site c P.length = 0 ∧
      (∀ j, 2 * P.diffusivity * c j =
        P.strength j * finiteKinkPotential F Finset.univ P.site c (P.site j)) := by
  exact ⟨hu.kinkBase, hu.kinkCoefficient, hu.kinkBase_contDiff, hu.kinkPotential_eq,
    fun _ hz => hu.kinkBase_curvature hz, hu.kinkSlope_endpoints.1,
    hu.kinkSlope_endpoints.2, hu.kinkPotential_reaction⟩

theorem SpectralProblem.interval_eigenstate_kink_representation (P : SpectralProblem n)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) :
    ∃ (F : ℝ → ℝ) (c : Fin n → ℝ), ContDiff ℝ 2 F ∧
      EqOn (finiteKinkPotential F Finset.univ P.site c)
        ((P.intervalPointProblem.eigenstate i).representative P.length_pos) (Icc 0 P.length) ∧
      (∀ z ∈ Icc 0 P.length, deriv (deriv F) z =
        -i.1⁻¹ * (P.intervalPointProblem.eigenstate i).representative P.length_pos z / P.diffusivity) ∧
      finiteKinkSlope F Finset.univ P.site c 0 = 0 ∧
      finiteKinkSlope F Finset.univ P.site c P.length = 0 ∧
      (∀ j, 2 * P.diffusivity * c j =
        P.strength j * finiteKinkPotential F Finset.univ P.site c (P.site j)) :=
  (P.interval_eigenbasis_weak i).kink_representation

end TimeTraps.Spectral
