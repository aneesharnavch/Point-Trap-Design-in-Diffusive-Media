module

public import TimeTraps.Probability.BrownianAffineRegulatorLocal

@[expose] public section

/-! The candidate regulator sums define actual Stieltjes measures.
Use a zero path outside the proved lattice event and extend by zero to
negative times. On that event the measures have the actual sum increments
and are supported on the corresponding deterministic folded boundary.
No reflected stochastic equation or Brownian-law identification is used. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def affineBrownianRegulatorRealPath (x σ L : ℝ) (b : ℤ) (t : ℝ) (ω : ℕ → ℝ) : ℝ := by
  classical
  exact if affineBrownianLatticeRegular x σ L ω then affineBrownianRegulator x σ L b t.toNNReal ω else 0

theorem affineBrownianRegulatorRealPath_continuous (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (b : ℤ) (ω : ℕ → ℝ) :
    Continuous (fun t => affineBrownianRegulatorRealPath x σ L b t ω) := by
  by_cases hω : affineBrownianLatticeRegular x σ L ω
  · simp only [affineBrownianRegulatorRealPath, if_pos hω]
    exact (affineBrownianRegulator_continuous hσ hL hω b).comp continuous_real_toNNReal
  · simp only [affineBrownianRegulatorRealPath, if_neg hω]
    exact continuous_const

theorem affineBrownianRegulatorRealPath_monotone (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (b : ℤ) (ω : ℕ → ℝ) :
    Monotone (fun t => affineBrownianRegulatorRealPath x σ L b t ω) := by
  by_cases hω : affineBrownianLatticeRegular x σ L ω
  · simp only [affineBrownianRegulatorRealPath, if_pos hω]
    exact (affineBrownianRegulator_monotone hσ hL hω b).comp Real.toNNReal_monotone
  · simp only [affineBrownianRegulatorRealPath, if_neg hω]
    exact monotone_const

theorem affineBrownianRegulatorRealPath_nonpos (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (L : ℝ) (b : ℤ) (ω : ℕ → ℝ) {t : ℝ} (ht : t ≤ 0) :
    affineBrownianRegulatorRealPath x σ L b t ω = 0 := by
  by_cases hω : affineBrownianLatticeRegular x σ L ω
  · simp only [affineBrownianRegulatorRealPath, if_pos hω, Real.toNNReal_of_nonpos ht,
      affineBrownianRegulator_zero hσ hω b]
  · exact if_neg hω

def affineBrownianRegulatorStieltjes (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (b : ℤ) (ω : ℕ → ℝ) : StieltjesFunction ℝ :=
  continuousStieltjesFunction (fun t => affineBrownianRegulatorRealPath x σ L b t ω)
    (affineBrownianRegulatorRealPath_monotone x hσ hL b ω)
    (affineBrownianRegulatorRealPath_continuous x hσ hL b ω)

def affineBrownianRegulatorTimeMeasure (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (b : ℤ) (ω : ℕ → ℝ) : Measure ℝ :=
  (affineBrownianRegulatorStieltjes x hσ hL b ω).measure

theorem affineBrownianRegulatorStieltjes_apply {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) (b : ℤ) (t : ℝ) :
    affineBrownianRegulatorStieltjes x hσ hL b ω t = affineBrownianRegulator x σ L b t.toNNReal ω :=
  if_pos hω

theorem affineBrownianRegulatorTimeMeasure_Ioc {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) (b : ℤ) (S T : ℝ) :
    affineBrownianRegulatorTimeMeasure x hσ hL b ω (Ioc S T) =
      ENNReal.ofReal (affineBrownianRegulator x σ L b T.toNNReal ω -
        affineBrownianRegulator x σ L b S.toNNReal ω) := by
  rw [affineBrownianRegulatorTimeMeasure, StieltjesFunction.measure_Ioc,
    affineBrownianRegulatorStieltjes_apply hσ hL hω b S,
    affineBrownianRegulatorStieltjes_apply hσ hL hω b T]

theorem affineBrownianRegulatorTimeMeasure_singleton (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (b : ℤ) (ω : ℕ → ℝ) (t : ℝ) :
    affineBrownianRegulatorTimeMeasure x hσ hL b ω {t} = 0 :=
  continuousStieltjesFunction_measure_singleton _ _ _ t

theorem affineBrownianRegulatorTimeMeasure_support {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) (b : ℤ) :
    (affineBrownianRegulatorTimeMeasure x hσ hL b ω).support ⊆
      {t : ℝ | 0 ≤ t ∧ reflectedFold L (affineBrownianInput x σ t.toNNReal ω) =
        reflectedFold L ((b : ℝ) * L)} := by
  intro t ht
  have hnonneg : 0 ≤ t := by
    by_contra hn
    have hneg : t < 0 := lt_of_not_ge hn
    have hflat : ∀ᶠ s in 𝓝 t,
        affineBrownianRegulatorRealPath x σ L b s ω = affineBrownianRegulatorRealPath x σ L b t ω := by
      filter_upwards [Iio_mem_nhds hneg] with s hs
      rw [affineBrownianRegulatorRealPath_nonpos x hσ L b ω (show s ≤ 0 from hs.le),
        affineBrownianRegulatorRealPath_nonpos x hσ L b ω hneg.le]
    exact (continuousStieltjesFunction_notMem_support _
      (affineBrownianRegulatorRealPath_monotone x hσ hL b ω)
      (affineBrownianRegulatorRealPath_continuous x hσ hL b ω) t hflat) ht
  refine ⟨hnonneg, ?_⟩
  by_contra hn
  have hlocal := affineBrownianRegulator_locally_constant hσ hL hω b t.toNNReal hn
  have hflat : ∀ᶠ s in 𝓝 t,
      affineBrownianRegulatorRealPath x σ L b s ω = affineBrownianRegulatorRealPath x σ L b t ω := by
    simp only [affineBrownianRegulatorRealPath, if_pos hω]
    exact continuous_real_toNNReal.continuousAt.tendsto.eventually hlocal
  exact (continuousStieltjesFunction_notMem_support _
    (affineBrownianRegulatorRealPath_monotone x hσ hL b ω)
    (affineBrownianRegulatorRealPath_continuous x hσ hL b ω) t hflat) ht

theorem affineBrownianRegulatorTimeMeasure_boundary_support {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) :
    ((affineBrownianRegulatorTimeMeasure x hσ hL 0 ω).support ⊆
      {t : ℝ | 0 ≤ t ∧ reflectedFold L (affineBrownianInput x σ t.toNNReal ω) = 0}) ∧
    ((affineBrownianRegulatorTimeMeasure x hσ hL 1 ω).support ⊆
      {t : ℝ | 0 ≤ t ∧ reflectedFold L (affineBrownianInput x σ t.toNNReal ω) = L}) := by
  constructor
  · simpa only [Int.cast_zero, zero_mul, reflectedFold_zero] using
      affineBrownianRegulatorTimeMeasure_support hσ hL hω 0
  · simpa only [Int.cast_one, one_mul, reflectedFold_eq_self L hL L ⟨hL.le, le_rfl⟩] using
      affineBrownianRegulatorTimeMeasure_support hσ hL hω 1

end TimeTraps.Probability

end
