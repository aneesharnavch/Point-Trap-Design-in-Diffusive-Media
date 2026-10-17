module

public import TimeTraps.Probability.ReflectedInteriorTanakaCorrection
public import TimeTraps.Analysis.ReflectedInteriorTanakaFinite

@[expose] public section

/-! The finite labelled kink correction is exactly the paired lattice
partial sum whose uniform finite-horizon stabilization has been proved. -/

namespace TimeTraps.Probability

open Set Filter MeasureTheory ProbabilityTheory TimeTraps.Analysis
open scoped NNReal Topology

theorem reflectedInteriorFinite_correction_sum (x σ L a : ℝ) (N : ℕ)
    (t : ℝ≥0) (ω : ℕ → ℝ) :
    (∑ i ∈ reflectedInteriorFiniteSet N, reflectedInteriorFiniteCoeff i *
      affineBrownianTanakaCorrection x σ (reflectedInteriorFiniteSite L a i) t ω) =
        reflectedInteriorTanakaCorrectionSum x σ L a N t ω := by
  have hm (q : ℝ) : affineBrownianTanakaCorrection (x - a) σ q t ω =
      affineBrownianTanakaCorrection x σ (q + a) t ω := by
    calc
      _ = affineBrownianTanakaCorrection (x + (-a)) σ q t ω := by rw [sub_eq_add_neg]
      _ = _ := (affineBrownianTanakaCorrection_translate x σ q (-a) t ω).trans
        (congrArg (fun z => affineBrownianTanakaCorrection x σ z t ω) (by ring))
  have hp (q : ℝ) : affineBrownianTanakaCorrection (x + a) σ q t ω =
      affineBrownianTanakaCorrection x σ (q - a) t ω :=
    affineBrownianTanakaCorrection_translate x σ q a t ω
  rw [reflectedInteriorFinite_sum L a N (fun q => affineBrownianTanakaCorrection x σ q t ω)]
  unfold reflectedInteriorTanakaCorrectionSum integerPairedPartialSum integerSplitPartialSum
  simp_rw [hm, hp]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_zero, Int.cast_one, Int.cast_ofNat,
    Int.cast_natCast, Int.cast_neg, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
    mul_zero, zero_mul, add_zero, zero_add, zero_sub]
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      ring_nf
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      ring_nf at ih ⊢
      linear_combination (norm := ring_nf) ih

end TimeTraps.Probability
