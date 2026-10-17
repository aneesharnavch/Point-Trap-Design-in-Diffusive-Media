module

public import TimeTraps.Probability.ReflectedRobinKilledSpectralSemigroup

@[expose] public section

/-! The generator of the actual killed expectation is precisely the
original full-H1 Robin operator, written with both boundary coefficients
and every original interior coefficient explicitly. -/

namespace TimeTraps.Probability

open Set TimeTraps.Analysis TimeTraps.Spectral IntervalSobolevSpace

variable {n : ℕ}

theorem reflectedRobinKilledInterval_generator_iff_robin (P : RobinProblem n)
    (f : IntervalSobolevL2 0 P.length) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 P.length) :
    HasDerivWithinAt (reflectedRobinKilledIntervalCurve P (ofEnergy hu P.length_pos).state) (-f) (Ici 0) 0 ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v 0 P.length →
        P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x) +
          (∑ i, P.strength i * u (P.site i) * v (P.site i)) +
          P.betaLeft * u 0 * v 0 + P.betaRight * u P.length * v P.length =
            ∫ x in (0 : ℝ)..P.length, f x * v x := by
  rw [reflectedRobinKilledInterval_generator_iff_physical]
  simp only [P.operator_pointForm]

end TimeTraps.Probability
