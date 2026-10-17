module

public import TimeTraps.Probability.ReflectedRegulatorIntegral
public import TimeTraps.Probability.BrownianFoldTanakaGlobal
public import TimeTraps.Probability.BrownianItoTaylorTelescope
public import TimeTraps.Probability.DyadicWeightedQuadraticVariationData

@[expose] public section

/-! Exact finite decomposition for the actual folded affine path.
The all-time path equation gives one event for every weight, horizon and
dyadic level. Taylor telescoping is purely algebraic and assumes no
smoothness or identification of the driver sums with an integral. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

noncomputable def affineBrownianFoldDriverWeightedSum (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  σ * ∑ i : Fin (2 ^ n),
    g (reflectedFold L (affineBrownianInput x σ (brownianDyadicGrid T n i.castSucc) ω)) *
      (brownianFoldSlopeGlobalPath L hL x hσ (brownianDyadicGrid T n i.succ) ω -
        brownianFoldSlopeGlobalPath L hL x hσ (brownianDyadicGrid T n i.castSucc) ω)

theorem affineBrownianFold_firstOrder_decomposition_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ),
      (∑ i : Fin (2 ^ n),
        g (reflectedFold L (affineBrownianInput x σ (brownianDyadicGrid T n i.castSucc) ω)) *
          (reflectedFold L (affineBrownianInput x σ (brownianDyadicGrid T n i.succ) ω) -
            reflectedFold L (affineBrownianInput x σ (brownianDyadicGrid T n i.castSucc) ω))) =
      affineBrownianFoldDriverWeightedSum L hL x hσ g T n ω +
        affineBrownianRegulatorWeightedSum x σ L 0 g T n ω -
          affineBrownianRegulatorWeightedSum x σ L 1 g T n ω := by
  filter_upwards [affineBrownianFoldTanaka_global_ae L hL x hσ] with ω hω
  intro g T n
  have hi (i : Fin (2 ^ n)) :
      reflectedFold L (affineBrownianInput x σ (brownianDyadicGrid T n i.succ) ω) -
        reflectedFold L (affineBrownianInput x σ (brownianDyadicGrid T n i.castSucc) ω) =
      σ * (brownianFoldSlopeGlobalPath L hL x hσ (brownianDyadicGrid T n i.succ) ω -
        brownianFoldSlopeGlobalPath L hL x hσ (brownianDyadicGrid T n i.castSucc) ω) +
      (affineBrownianRegulator x σ L 0 (brownianDyadicGrid T n i.succ) ω -
        affineBrownianRegulator x σ L 0 (brownianDyadicGrid T n i.castSucc) ω) -
      (affineBrownianRegulator x σ L 1 (brownianDyadicGrid T n i.succ) ω -
        affineBrownianRegulator x σ L 1 (brownianDyadicGrid T n i.castSucc) ω) := by
    rw [hω (brownianDyadicGrid T n i.succ), hω (brownianDyadicGrid T n i.castSucc)]
    unfold affineBrownianLowerRegulator affineBrownianUpperRegulator
    ring
  unfold affineBrownianFoldDriverWeightedSum affineBrownianRegulatorWeightedSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i]
  ring

theorem affineBrownianFold_finite_taylor_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (F : ℝ → ℝ) (T : ℝ≥0) (n : ℕ),
      F (reflectedFold L (affineBrownianInput x σ T ω)) - F (reflectedFold L x) =
      affineBrownianFoldDriverWeightedSum L hL x hσ (deriv F) T n ω +
        affineBrownianRegulatorWeightedSum x σ L 0 (deriv F) T n ω -
          affineBrownianRegulatorWeightedSum x σ L 1 (deriv F) T n ω +
        (1 / 2 : ℝ) * dyadicWeightedPathQV
          (fun t => reflectedFold L (affineBrownianInput x σ t ω))
          (fun t => deriv (deriv F) (reflectedFold L (affineBrownianInput x σ t ω))) T n +
        brownianItoTaylorSum (Ω := ℕ → ℝ)
          (fun t ω => reflectedFold L (affineBrownianInput x σ t ω)) F (N := 2 ^ n)
          (brownianDyadicGrid T n) ω := by
  filter_upwards [affineBrownianFold_firstOrder_decomposition_ae L hL x hσ,
    affineBrownianInput_start x σ] with ω hsum hzero
  intro F T n
  have he := ito_finite_taylor F (fun i : Fin (2 ^ n + 1) =>
    reflectedFold L (affineBrownianInput x σ (brownianDyadicGrid T n i) ω))
  rw [brownianDyadicGrid_zero, brownianDyadicGrid_last, hzero] at he
  rw [hsum (deriv F) T n] at he
  exact he

end TimeTraps.Probability
