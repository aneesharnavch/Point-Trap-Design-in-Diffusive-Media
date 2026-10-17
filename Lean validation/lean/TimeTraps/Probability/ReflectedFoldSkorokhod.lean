module

public import TimeTraps.Analysis.TwoBoundarySkorokhodRegulators
public import TimeTraps.Probability.ReflectedFoldRegulatorPaths
public import TimeTraps.Probability.BrownianFoldTanakaGlobal

@[expose] public section

/-! The actual folded affine trajectory and the even/odd Tanaka sums
solve the deterministic two-boundary problem driven by the constructed
continuous slope integral. They are the unique confined path and
regulators for that input. Real-time paths use the canonical extension
through `toNNReal`; the final comparison is stated at every nonnegative
time. No law of the driving integral is needed. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def reflectedFoldSkorokhodInput (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (t : ℝ) (ω : ℕ → ℝ) : ℝ :=
  reflectedFold L x + σ * brownianFoldSlopeGlobalPath L hL x hσ t.toNNReal ω

theorem reflectedFoldSkorokhodInput_continuous (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (ω : ℕ → ℝ) :
    Continuous (fun t => reflectedFoldSkorokhodInput L hL x hσ t ω) :=
  continuous_const.add (continuous_const.mul
    ((brownianFoldSlopeGlobalPath_continuous L hL x hσ ω).comp continuous_real_toNNReal))

theorem reflectedFoldSkorokhodInput_zero (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (ω : ℕ → ℝ) :
    reflectedFoldSkorokhodInput L hL x hσ 0 ω = reflectedFold L x := by
  simp only [reflectedFoldSkorokhodInput, Real.toNNReal_zero,
    brownianFoldSlopeGlobalPath_zero, mul_zero, add_zero]

theorem reflectedFoldSkorokhod_ae (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      TwoBoundarySkorokhodStieltjes L (fun t => reflectedFoldSkorokhodInput L hL x hσ t ω)
        (fun t => reflectedFold L (affineBrownianInput x σ t.toNNReal ω))
        (affineBrownianRegulatorStieltjes x hσ hL 0 ω)
        (affineBrownianRegulatorStieltjes x hσ hL 1 ω) := by
  filter_upwards [reflectedFoldRegulatorRegular_ae x σ L,
    affineBrownianFoldTanaka_global_ae L hL x hσ] with ω hr he
  have hp := reflectedFoldRegulatorPaths_of_regular hσ hL hr
  refine ⟨hp.path_continuous.comp continuous_real_toNNReal,
    affineBrownianRegulatorRealPath_continuous x hσ hL 0 ω,
    affineBrownianRegulatorRealPath_continuous x hσ hL 1 ω,
    affineBrownianRegulatorRealPath_nonpos x hσ L 0 ω le_rfl,
    affineBrownianRegulatorRealPath_nonpos x hσ L 1 ω le_rfl,
    fun t _ => hp.confined t.toNNReal, ?_, hp.lower_support, hp.upper_support⟩
  intro t _
  rw [affineBrownianRegulatorStieltjes_apply hσ hL hr.1 0 t,
    affineBrownianRegulatorStieltjes_apply hσ hL hr.1 1 t]
  exact he t.toNNReal

theorem reflectedFoldSkorokhod_unique_ae (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (X : ℝ → ℝ) (lower upper : StieltjesFunction ℝ),
      TwoBoundarySkorokhodStieltjes L (fun t => reflectedFoldSkorokhodInput L hL x hσ t ω)
        X lower upper → ∀ t : ℝ≥0,
      X t = reflectedFold L (affineBrownianInput x σ t ω) ∧
        lower t = affineBrownianLowerRegulator x σ L t ω ∧
        upper t = affineBrownianUpperRegulator x σ L t ω := by
  filter_upwards [reflectedFoldSkorokhod_ae L hL x hσ,
    affineBrownianLatticeRegular_ae x σ L] with ω ha hr
  intro X lower upper hc t
  have he := twoBoundarySkorokhodStieltjes_unique_all hL hc ha
  have ht : (t : ℝ) ∈ Ici (0 : ℝ) := t.property
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Real.toNNReal_coe] using he.1 ht
  · simpa only [affineBrownianRegulatorStieltjes_apply hσ hL hr 0,
      Real.toNNReal_coe, affineBrownianLowerRegulator] using he.2.1 ht
  · simpa only [affineBrownianRegulatorStieltjes_apply hσ hL hr 1,
      Real.toNNReal_coe, affineBrownianUpperRegulator] using he.2.2 ht

end TimeTraps.Probability

end
