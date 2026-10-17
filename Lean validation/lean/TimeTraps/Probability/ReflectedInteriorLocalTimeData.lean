module

public import TimeTraps.Probability.BrownianAffineRegulatorStieltjes
public import TimeTraps.Analysis.ReflectedFoldDensityPreimage

@[expose] public section

/-! A candidate interior correction is the sum of the two actual shifted
lower regulators. Its periodized affine local-time formula is exact,
including the doubled endpoint values. Division by sigma squared defines
a prospective occupation coefficient; no occupation or Tanaka identity
for the folded path is asserted here. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

noncomputable def reflectedInteriorCorrection (x σ L a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  affineBrownianLowerRegulator (x - a) σ L t ω + affineBrownianLowerRegulator (x + a) σ L t ω

noncomputable def reflectedInteriorOccupationCoefficient (x σ L a : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  reflectedInteriorCorrection x σ L a t ω / σ ^ 2

theorem affineBrownianTanakaCorrection_translate (x σ a c : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    affineBrownianTanakaCorrection (x + c) σ a t ω =
      affineBrownianTanakaCorrection x σ (a - c) t ω := by
  have he : (a - (x + c)) / σ = (a - c - x) / σ := by ring
  exact congrArg (fun z : ℝ => σ * brownianLocalTimeTimeField z t ω) he

theorem reflectedInteriorCorrection_periodized (x σ L a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedInteriorCorrection x σ L a t ω =
      (∑' k : ℤ, affineBrownianTanakaCorrection x σ (a + (k : ℝ) * (2 * L)) t ω) +
      ∑' k : ℤ, affineBrownianTanakaCorrection x σ (-a + (k : ℝ) * (2 * L)) t ω := by
  unfold reflectedInteriorCorrection affineBrownianLowerRegulator affineBrownianRegulator
  apply congrArg₂ (fun u v : ℝ => u + v)
  · apply tsum_congr
    intro k
    have he : (((2 * k + 0 : ℤ) : ℝ) * L) - (-a) = a + (k : ℝ) * (2 * L) := by
      push_cast
      ring
    calc
      _ = affineBrownianTanakaCorrection (x + (-a)) σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω := by
        rw [sub_eq_add_neg]
      _ = _ := (affineBrownianTanakaCorrection_translate x σ _ (-a) t ω).trans
        (congrArg (fun z : ℝ => affineBrownianTanakaCorrection x σ z t ω) he)
  · apply tsum_congr
    intro k
    have he : (((2 * k + 0 : ℤ) : ℝ) * L) - a = -a + (k : ℝ) * (2 * L) := by
      push_cast
      ring
    exact (affineBrownianTanakaCorrection_translate x σ _ a t ω).trans
      (congrArg (fun z : ℝ => affineBrownianTanakaCorrection x σ z t ω) he)

theorem affineBrownianLowerRegulator_sub_length (x σ L : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    affineBrownianLowerRegulator (x - L) σ L t ω = affineBrownianUpperRegulator x σ L t ω := by
  unfold affineBrownianLowerRegulator affineBrownianUpperRegulator affineBrownianRegulator
  apply tsum_congr
  intro k
  have he : (((2 * k + 0 : ℤ) : ℝ) * L) - (-L) = ((2 * k + 1 : ℤ) : ℝ) * L := by
    push_cast
    ring
  calc
    _ = affineBrownianTanakaCorrection (x + (-L)) σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω := by
      rw [sub_eq_add_neg]
    _ = _ := (affineBrownianTanakaCorrection_translate x σ _ (-L) t ω).trans
      (congrArg (fun z : ℝ => affineBrownianTanakaCorrection x σ z t ω) he)

theorem affineBrownianLowerRegulator_add_length (x σ L : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    affineBrownianLowerRegulator (x + L) σ L t ω = affineBrownianUpperRegulator x σ L t ω := by
  unfold affineBrownianLowerRegulator affineBrownianUpperRegulator affineBrownianRegulator
  calc
    _ = ∑' k : ℤ, affineBrownianTanakaCorrection x σ
        (((2 * (k + (-1)) + 1 : ℤ) : ℝ) * L) t ω := by
      apply tsum_congr
      intro k
      have he : (((2 * k + 0 : ℤ) : ℝ) * L) - L = ((2 * (k + (-1)) + 1 : ℤ) : ℝ) * L := by
        push_cast
        ring
      exact (affineBrownianTanakaCorrection_translate x σ _ L t ω).trans
        (congrArg (fun z : ℝ => affineBrownianTanakaCorrection x σ z t ω) he)
    _ = _ := (Equiv.addRight (-1 : ℤ)).tsum_eq
      (fun k : ℤ => affineBrownianTanakaCorrection x σ (((2 * k + 1 : ℤ) : ℝ) * L) t ω)

theorem reflectedInteriorCorrection_left (x σ L : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedInteriorCorrection x σ L 0 t ω = 2 * affineBrownianLowerRegulator x σ L t ω := by
  simp only [reflectedInteriorCorrection, sub_zero, add_zero]
  ring

theorem reflectedInteriorCorrection_right (x σ L : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedInteriorCorrection x σ L L t ω = 2 * affineBrownianUpperRegulator x σ L t ω := by
  rw [reflectedInteriorCorrection, affineBrownianLowerRegulator_sub_length,
    affineBrownianLowerRegulator_add_length]
  ring

theorem reflectedInteriorOccupationCoefficient_normalization (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (L a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    σ ^ 2 * reflectedInteriorOccupationCoefficient x σ L a t ω =
      reflectedInteriorCorrection x σ L a t ω := by
  unfold reflectedInteriorOccupationCoefficient
  exact mul_div_cancel₀ _ (pow_ne_zero _ hσ.ne')

end TimeTraps.Probability
