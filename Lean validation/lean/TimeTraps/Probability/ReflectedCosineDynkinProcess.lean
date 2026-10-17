module

public import TimeTraps.Probability.ReflectedCosineDynkinData

@[expose] public section

/-! The literal compensated Neumann-cosine process. The compensator is
the genuine ordinary time integral, and its raw-past measurability is
explicitly almost everywhere. The physical second-derivative formula
retains the actual initial state. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable def reflectedCosineDynkin {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L D x : ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  reflectedCosineInput L D x n (B t ω) - reflectedCosineInput L D x n (B 0 ω) +
    (D * ((n : ℝ) * Real.pi / L) ^ 2) * brownianItoDrift B (reflectedCosineInput L D x n) t ω

theorem reflectedCosineDynkin_zero {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L D x : ℝ) (n : ℕ) (ω : Ω) : reflectedCosineDynkin B L D x n 0 ω = 0 := by
  simp only [reflectedCosineDynkin, brownianItoDrift_zero, sub_self, mul_zero, add_zero]

theorem reflectedCosineDynkin_physical {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    reflectedCosineDynkin B L D x n t ω =
      Real.cos (((n : ℝ) * Real.pi / L) * foldedTrajectory L D x B t ω) -
        Real.cos (((n : ℝ) * Real.pi / L) * foldedTrajectory L D x B 0 ω) -
      D * (∫ r in (0 : ℝ)..t.val,
        deriv (deriv (fun z : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * z)))
          (foldedTrajectory L D x B r.toNNReal ω)) := by
  have hi : D * (∫ r in (0 : ℝ)..t.val,
      deriv (deriv (fun z : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * z)))
        (foldedTrajectory L D x B r.toNNReal ω)) =
      (-D * ((n : ℝ) * Real.pi / L) ^ 2) * brownianItoDrift B (reflectedCosineInput L D x n) t ω := by
    rw [← intervalIntegral.integral_const_mul]
    have he : (fun r : ℝ => D * deriv (deriv
        (fun z : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * z)))
          (foldedTrajectory L D x B r.toNNReal ω)) =
        (fun r : ℝ => (-D * ((n : ℝ) * Real.pi / L) ^ 2) *
          reflectedCosineInput L D x n (B r.toNNReal ω)) := by
      funext r
      rw [reflectedCosine_spatial_eigenvalue, reflectedCosineInput_folded L hL]
    rw [he, intervalIntegral.integral_const_mul]
    rfl
  rw [hi]
  unfold reflectedCosineDynkin
  rw [reflectedCosineInput_folded L hL, reflectedCosineInput_folded L hL]
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem reflectedCosineDynkin_memLp (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L D x : ℝ) (n : ℕ) (t : ℝ≥0) : MemLp (reflectedCosineDynkin B L D x n t) 2 P := by
  have hg := reflectedCosineInput_lipschitz L D x n
  exact ((brownianLipschitz_eval_memLp hB hg t).sub (brownianLipschitz_eval_memLp hB hg 0)).add
    ((brownianItoDrift_memLp hB hg hjoint t).const_mul _)

theorem reflectedCosineDynkin_aestronglyMeasurable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L D x : ℝ) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (reflectedCosineDynkin B L D x n t) P := by
  have hg := reflectedCosineInput_lipschitz L D x n
  have ht := hg.continuous.comp_stronglyMeasurable (brownianNaturalFiltration_stronglyAdapted B hBm t)
  have h0 := hg.continuous.comp_stronglyMeasurable
    ((brownianNaturalFiltration_stronglyAdapted B hBm 0).mono
      ((brownianNaturalFiltration B hBm).mono (show (0 : ℝ≥0) ≤ t from zero_le)))
  exact (ht.sub h0).aestronglyMeasurable.add
    ((brownianItoDrift_aestronglyMeasurable_past hB hBm hg hjoint t).const_mul _)

end TimeTraps.Probability
