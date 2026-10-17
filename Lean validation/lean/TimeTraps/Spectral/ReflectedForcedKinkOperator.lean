module

public import TimeTraps.Spectral.ReflectedForcedKinkBridge
public import TimeTraps.Spectral.IntervalOperatorBridge
public import TimeTraps.Analysis.IntervalSobolevCompactL2

@[expose] public section

/-! The existing physical interval solution operator applied to a
continuous source has the derived global C²-plus-finite-kinks
representation. The L2 source represents the same function almost
everywhere; no eigenstate, source positivity, or extra smoothness is used. -/

noncomputable section

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

def SpectralProblem.forcedSourceL2 (P : SpectralProblem n) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 P.length)) : IntervalSobolevL2 0 P.length :=
  continuousL2 P.length_pos (forcedKinkSource P g hg)

def SpectralProblem.forcedSolution (P : SpectralProblem n) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 P.length)) : IntervalSobolevSpace 0 P.length :=
  P.intervalPointProblem.solution (P.forcedSourceL2 g hg)

def SpectralProblem.forcedSolutionState (P : SpectralProblem n) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 P.length)) : ℝ → ℝ :=
  (P.forcedSolution g hg).representative P.length_pos

theorem SpectralProblem.forcedSourceL2_ae (P : SpectralProblem n) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 P.length)) :
    P.forcedSourceL2 g hg =ᵐ[volume.restrict (Ioo 0 P.length)] g := by
  filter_upwards [continuousL2_ae P.length_pos (forcedKinkSource P g hg),
    ae_restrict_mem measurableSet_Ioo] with x he hx
  change (continuousL2 P.length_pos (forcedKinkSource P g hg)) x = g x
  rw [he, projIcc_of_mem P.length_pos.le (Ioo_subset_Icc_self hx)]
  rfl

theorem SpectralProblem.forcedSolution_weak (P : SpectralProblem n) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 P.length)) :
    WeakForcedEquation P g (P.forcedSolutionState g hg) := by
  refine ⟨((P.forcedSolution g hg).representative_spec P.length_pos).1, ?_⟩
  intro v hv
  have he := P.intervalPointProblem.solution_physical (P.forcedSourceL2 g hg) v hv
  change intervalPointForm P.diffusivity P.strength P.site 0 P.length
    (P.forcedSolutionState g hg) v =
      ∫ x in (0 : ℝ)..P.length, (P.forcedSourceL2 g hg) x * v x at he
  refine he.trans ?_
  simp only [intervalIntegral.integral_of_le P.length_pos.le, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [P.forcedSourceL2_ae g hg] with x hx
  rw [hx]

theorem SpectralProblem.forcedSolution_kink_representation (P : SpectralProblem n)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 P.length)) :
    ∃ (F : ℝ → ℝ) (c : Fin n → ℝ), ContDiff ℝ 2 F ∧
      EqOn (finiteKinkPotential F Finset.univ P.site c) (P.forcedSolutionState g hg)
        (Icc 0 P.length) ∧
      (∀ z ∈ Icc 0 P.length, P.diffusivity * deriv (deriv F) z = -g z) ∧
      finiteKinkSlope F Finset.univ P.site c 0 = 0 ∧
      finiteKinkSlope F Finset.univ P.site c P.length = 0 ∧
      (∀ i, 2 * P.diffusivity * c i = P.strength i * P.forcedSolutionState g hg (P.site i)) ∧
      (∀ i, 2 * P.diffusivity * c i =
        P.strength i * finiteKinkPotential F Finset.univ P.site c (P.site i)) :=
  (P.forcedSolution_weak g hg).kink_representation hg

end TimeTraps.Spectral

end
