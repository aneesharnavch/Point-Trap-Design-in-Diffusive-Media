module

public import TimeTraps.Probability.BrownianAffineRegulatorStieltjes

@[expose] public section

/-! A practical path bundle for the actual folded affine input and its
actual even/odd Tanaka-correction sums. One measurable full-probability
event gives confinement, initial value, regulator regularity, exact
Stieltjes increments and boundary support. The path equation and any
Skorokhod uniqueness or Brownian-law assertion are deliberately separate. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

def reflectedFoldRegulatorRegular (x σ L : ℝ) (ω : ℕ → ℝ) : Prop :=
  affineBrownianLatticeRegular x σ L ω ∧ brownianDyadicPath 0 ω = 0

structure ReflectedFoldRegulatorPaths (x σ L : ℝ) (hσ : 0 < σ) (hL : 0 < L)
    (ω : ℕ → ℝ) : Prop where
  path_continuous : Continuous (fun t => reflectedFold L (affineBrownianInput x σ t ω))
  confined : ∀ t : ℝ≥0, reflectedFold L (affineBrownianInput x σ t ω) ∈ Icc 0 L
  initial : reflectedFold L (affineBrownianInput x σ 0 ω) = reflectedFold L x
  lower_continuous : Continuous (fun t => affineBrownianLowerRegulator x σ L t ω)
  lower_monotone : Monotone (fun t => affineBrownianLowerRegulator x σ L t ω)
  lower_zero : affineBrownianLowerRegulator x σ L 0 ω = 0
  lower_nonneg : ∀ t : ℝ≥0, 0 ≤ affineBrownianLowerRegulator x σ L t ω
  upper_continuous : Continuous (fun t => affineBrownianUpperRegulator x σ L t ω)
  upper_monotone : Monotone (fun t => affineBrownianUpperRegulator x σ L t ω)
  upper_zero : affineBrownianUpperRegulator x σ L 0 ω = 0
  upper_nonneg : ∀ t : ℝ≥0, 0 ≤ affineBrownianUpperRegulator x σ L t ω
  lower_increment : ∀ S T : ℝ,
    affineBrownianRegulatorTimeMeasure x hσ hL 0 ω (Ioc S T) =
      ENNReal.ofReal (affineBrownianLowerRegulator x σ L T.toNNReal ω -
        affineBrownianLowerRegulator x σ L S.toNNReal ω)
  upper_increment : ∀ S T : ℝ,
    affineBrownianRegulatorTimeMeasure x hσ hL 1 ω (Ioc S T) =
      ENNReal.ofReal (affineBrownianUpperRegulator x σ L T.toNNReal ω -
        affineBrownianUpperRegulator x σ L S.toNNReal ω)
  lower_support : (affineBrownianRegulatorTimeMeasure x hσ hL 0 ω).support ⊆
    {t : ℝ | 0 ≤ t ∧ reflectedFold L (affineBrownianInput x σ t.toNNReal ω) = 0}
  upper_support : (affineBrownianRegulatorTimeMeasure x hσ hL 1 ω).support ⊆
    {t : ℝ | 0 ≤ t ∧ reflectedFold L (affineBrownianInput x σ t.toNNReal ω) = L}

theorem reflectedFoldRegulatorRegular_measurableSet (x σ L : ℝ) :
    MeasurableSet {ω | reflectedFoldRegulatorRegular x σ L ω} :=
  (affineBrownianLatticeRegular_measurableSet x σ L).inter
    (measurableSet_eq_fun (brownianDyadicPath_measurable 0) measurable_const)

theorem reflectedFoldRegulatorRegular_ae (x σ L : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, reflectedFoldRegulatorRegular x σ L ω :=
  (affineBrownianLatticeRegular_ae x σ L).and brownianDyadicPath_start_zero

theorem reflectedFoldRegulatorPaths_of_regular {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : reflectedFoldRegulatorRegular x σ L ω) :
    ReflectedFoldRegulatorPaths x σ L hσ hL ω := by
  refine ⟨(reflectedFold_continuous L).comp
      (affineBrownianInput_continuous x σ (hω.1 0).2.1),
    fun t => reflectedFold_mem L hL _, ?_,
    affineBrownianRegulator_continuous hσ hL hω.1 0,
    affineBrownianRegulator_monotone hσ hL hω.1 0,
    affineBrownianRegulator_zero hσ hω.1 0,
    fun t => affineBrownianRegulator_nonneg x hσ L 0 t ω,
    affineBrownianRegulator_continuous hσ hL hω.1 1,
    affineBrownianRegulator_monotone hσ hL hω.1 1,
    affineBrownianRegulator_zero hσ hω.1 1,
    fun t => affineBrownianRegulator_nonneg x hσ L 1 t ω,
    fun S T => affineBrownianRegulatorTimeMeasure_Ioc hσ hL hω.1 0 S T,
    fun S T => affineBrownianRegulatorTimeMeasure_Ioc hσ hL hω.1 1 S T,
    (affineBrownianRegulatorTimeMeasure_boundary_support hσ hL hω.1).1,
    (affineBrownianRegulatorTimeMeasure_boundary_support hσ hL hω.1).2⟩
  rw [affineBrownianInput, hω.2, mul_zero, add_zero]

theorem reflectedFoldRegulatorPaths_ae (x : ℝ) {σ L : ℝ} (hσ : 0 < σ) (hL : 0 < L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ReflectedFoldRegulatorPaths x σ L hσ hL ω :=
  (reflectedFoldRegulatorRegular_ae x σ L).mono
    (fun _ hω => reflectedFoldRegulatorPaths_of_regular hσ hL hω)

end TimeTraps.Probability
