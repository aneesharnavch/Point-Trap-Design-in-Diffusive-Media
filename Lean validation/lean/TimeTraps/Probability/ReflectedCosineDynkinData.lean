module

public import TimeTraps.Probability.ReflectedFoldCosineEvolution
public import TimeTraps.Probability.BrownianItoDriftAdapted
public import TimeTraps.Probability.BrownianOccupationTimeBound
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! The Neumann cosine observable as an actual bounded Lipschitz
function of the original Brownian input. Folding leaves this observable
unchanged, including at the reflecting endpoints. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable def reflectedCosineInput (L D x : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  Real.cos (((n : ℝ) * Real.pi / L) * (x + Real.sqrt (2 * D) * z))

theorem reflectedCosineInput_bound (L D x : ℝ) (n : ℕ) (z : ℝ) :
    |reflectedCosineInput L D x n z| ≤ 1 := Real.abs_cos_le_one _

theorem reflectedCosineInput_lipschitz (L D x : ℝ) (n : ℕ) :
    LipschitzWith ‖((n : ℝ) * Real.pi / L) * Real.sqrt (2 * D)‖₊
      (reflectedCosineInput L D x n) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  calc
    _ ≤ dist (((n : ℝ) * Real.pi / L) * (x + Real.sqrt (2 * D) * z))
        (((n : ℝ) * Real.pi / L) * (x + Real.sqrt (2 * D) * w)) := by
      simpa only [reflectedCosineInput, NNReal.coe_one, one_mul] using Real.lipschitzWith_cos.dist_le_mul
        (((n : ℝ) * Real.pi / L) * (x + Real.sqrt (2 * D) * z))
        (((n : ℝ) * Real.pi / L) * (x + Real.sqrt (2 * D) * w))
    _ = _ := by
      rw [Real.dist_eq, Real.dist_eq]
      rw [show ((n : ℝ) * Real.pi / L) * (x + Real.sqrt (2 * D) * z) -
        ((n : ℝ) * Real.pi / L) * (x + Real.sqrt (2 * D) * w) =
        (((n : ℝ) * Real.pi / L) * Real.sqrt (2 * D)) * (z - w) by ring, abs_mul]
      rfl

theorem reflectedCosineInput_folded {ι Ω : Type*} (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (n : ℕ) (B : ι → Ω → ℝ) (t : ι) (ω : Ω) :
    reflectedCosineInput L D x n (B t ω) =
      Real.cos (((n : ℝ) * Real.pi / L) * foldedTrajectory L D x B t ω) :=
  (foldedTrajectory_cosine L hL D x B n t ω).symm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem reflectedCosineInput_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (n : ℕ) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => reflectedCosineInput L D x n (B t ω) | brownianNaturalFiltration B hBm s] =ᵐ[P]
      (fun ω => Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * (t.val - s.val)) *
        reflectedCosineInput L D x n (B s ω)) := by
  simpa only [← reflectedCosineInput_folded L hL D x n B] using
    foldedTrajectory_cosine_condExp hB hBm L hL D hD x n hst

end TimeTraps.Probability
