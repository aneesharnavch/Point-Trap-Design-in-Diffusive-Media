module

public import TimeTraps.Probability.StieltjesBoundaryIntegral
public import TimeTraps.Probability.ReflectedFoldRegulatorPaths

@[expose] public section

/-! Actual regulator contributions to the reflected Itô formula.
Continuous spatial weights have convergent left sums against the actual
regulator increments. Boundary support identifies their limits with the
endpoint weight times the terminal regulator. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable def affineBrownianRegulatorWeightedSum (x σ L : ℝ) (b : ℤ)
    (g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ i : Fin (2 ^ n),
    (affineBrownianRegulator x σ L b (brownianDyadicGrid T n i.succ) ω -
      affineBrownianRegulator x σ L b (brownianDyadicGrid T n i.castSucc) ω) *
        g (reflectedFold L (affineBrownianInput x σ (brownianDyadicGrid T n i.castSucc) ω))

theorem affineBrownianRegulatorStieltjes_apply_nnreal {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω)
    (b : ℤ) (t : ℝ≥0) :
    affineBrownianRegulatorStieltjes x hσ hL b ω t.val = affineBrownianRegulator x σ L b t ω := by
  calc
    _ = affineBrownianRegulator x σ L b (t : ℝ).toNNReal ω :=
      affineBrownianRegulatorStieltjes_apply hσ hL hω b (t : ℝ)
    _ = _ := congrArg (fun s => affineBrownianRegulator x σ L b s ω)
      (Real.toNNReal_coe : (t : ℝ).toNNReal = t)

theorem affineBrownianRegulatorWeightedSum_eq_stieltjes {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω)
    (b : ℤ) (g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) :
    affineBrownianRegulatorWeightedSum x σ L b g T n ω =
      dyadicStieltjesSum (affineBrownianRegulatorStieltjes x hσ hL b ω)
        (fun t => g (reflectedFold L (affineBrownianInput x σ t ω))) T n := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg₂ (fun u v => (u - v) *
    g (reflectedFold L (affineBrownianInput x σ (brownianDyadicGrid T n i.castSucc) ω)))
    (affineBrownianRegulatorStieltjes_apply_nnreal hσ hL hω b (brownianDyadicGrid T n i.succ)).symm
    (affineBrownianRegulatorStieltjes_apply_nnreal hσ hL hω b (brownianDyadicGrid T n i.castSucc)).symm

theorem affineBrownianRegulator_weighted_integral {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω)
    (b : ℤ) (g : ℝ → ℝ) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val,
      g (reflectedFold L (affineBrownianInput x σ r.toNNReal ω))
        ∂affineBrownianRegulatorTimeMeasure x hσ hL b ω) =
      g (reflectedFold L ((b : ℝ) * L)) * affineBrownianRegulator x σ L b T ω := by
  have hs : (affineBrownianRegulatorStieltjes x hσ hL b ω).measure.support ⊆
      {r : ℝ | reflectedFold L (affineBrownianInput x σ r.toNNReal ω) =
        reflectedFold L ((b : ℝ) * L)} :=
    fun _ hr => (affineBrownianRegulatorTimeMeasure_support hσ hL hω b hr).2
  have he := stieltjes_integral_of_supported_level (affineBrownianRegulatorStieltjes x hσ hL b ω)
    (fun r => reflectedFold L (affineBrownianInput x σ r.toNNReal ω))
    (reflectedFold L ((b : ℝ) * L)) hs g T
  have hk : affineBrownianRegulatorStieltjes x hσ hL b ω T.val -
      affineBrownianRegulatorStieltjes x hσ hL b ω 0 = affineBrownianRegulator x σ L b T ω := by
    calc
      _ = affineBrownianRegulator x σ L b T ω - affineBrownianRegulator x σ L b 0 ω :=
        congrArg₂ (fun u v : ℝ => u - v)
          (affineBrownianRegulatorStieltjes_apply_nnreal hσ hL hω b T)
          (affineBrownianRegulatorStieltjes_apply_nnreal hσ hL hω b 0)
      _ = _ := sub_eq_self.mpr (affineBrownianRegulator_zero hσ hω b)
  exact he.trans (congrArg (fun z => g (reflectedFold L ((b : ℝ) * L)) * z) hk)

theorem affineBrownianRegulatorWeightedSum_tendsto {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω)
    (b : ℤ) (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    Tendsto (fun n => affineBrownianRegulatorWeightedSum x σ L b g T n ω) atTop
      (𝓝 (g (reflectedFold L ((b : ℝ) * L)) * affineBrownianRegulator x σ L b T ω)) := by
  have hc : Continuous (fun t => g (reflectedFold L (affineBrownianInput x σ t ω))) :=
    hg.comp ((reflectedFold_continuous L).comp (affineBrownianInput_continuous x σ (hω 0).2.1))
  have h := dyadicStieltjesSum_tendsto (affineBrownianRegulatorStieltjes x hσ hL b ω)
    (fun t => g (reflectedFold L (affineBrownianInput x σ t ω))) hc T
  have he := affineBrownianRegulator_weighted_integral hσ hL hω b g T
  have hf : (fun n => affineBrownianRegulatorWeightedSum x σ L b g T n ω) =
      dyadicStieltjesSum (affineBrownianRegulatorStieltjes x hσ hL b ω)
        (fun t => g (reflectedFold L (affineBrownianInput x σ t ω))) T :=
    funext (affineBrownianRegulatorWeightedSum_eq_stieltjes hσ hL hω b g T)
  rw [hf]
  convert h using 1
  exact congrArg (fun z : ℝ => 𝓝 z) he.symm

theorem affineBrownianRegulatorWeightedSum_boundary_ae (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun n => affineBrownianRegulatorWeightedSum x σ L 0 g T n ω) atTop
        (𝓝 (g 0 * affineBrownianLowerRegulator x σ L T ω)) ∧
      Tendsto (fun n => affineBrownianRegulatorWeightedSum x σ L 1 g T n ω) atTop
        (𝓝 (g L * affineBrownianUpperRegulator x σ L T ω)) := by
  filter_upwards [affineBrownianLatticeRegular_ae x σ L] with ω hω
  constructor
  · simpa only [affineBrownianLowerRegulator, Int.cast_zero, zero_mul, reflectedFold_zero] using
      affineBrownianRegulatorWeightedSum_tendsto hσ hL hω 0 g hg T
  · simpa only [affineBrownianUpperRegulator, Int.cast_one, one_mul,
      reflectedFold_eq_self L hL L ⟨hL.le, le_rfl⟩] using
      affineBrownianRegulatorWeightedSum_tendsto hσ hL hω 1 g hg T

end TimeTraps.Probability
