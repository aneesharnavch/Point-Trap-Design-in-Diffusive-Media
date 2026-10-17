module

public import TimeTraps.Probability.ReflectedKilledEigenbasis
public import TimeTraps.Analysis.GeneralIntervalPointHeat

@[expose] public section

/-! The killed operator built from literal stochastic expectations is
the spectral heat semigroup of the original weak point-contact operator.
Equality is derived on the complete eigenbasis and extended by continuity;
neither the spectral definition nor a semigroup law is assumed in the
construction of the stochastic operator. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral IntervalSobolevSpace
open scoped NNReal ENNReal Topology

variable {n : ℕ}

theorem reflectedKilledIntervalL2Operator_hasSum (P : SpectralProblem n) (T : ℝ≥0)
    (f : IntervalSobolevL2 0 P.length) :
    HasSum (fun i : CompactSpectralIndex P.intervalPointProblem.inverse =>
      (compactHeatCoefficient T i * inner ℝ (P.intervalPointProblem.eigenbasis i) f) •
        P.intervalPointProblem.eigenbasis i) (reflectedKilledIntervalL2Operator P T f) := by
  have h := (P.intervalPointProblem.eigenbasis_expansion f).mapL (reflectedKilledIntervalL2Operator P T)
  have hc (i : CompactSpectralIndex P.intervalPointProblem.inverse) :
      Real.exp (-i.1⁻¹ * T.val) = compactHeatCoefficient T i := by
    unfold compactHeatCoefficient
    apply congrArg Real.exp
    exact (neg_mul _ _).trans ((congrArg Neg.neg (mul_comm _ _)).trans
      ((neg_mul _ _).symm.trans (div_eq_mul_inv _ _).symm))
  apply h.congr
  intro s
  apply Finset.sum_congr rfl
  intro i _hi
  change reflectedKilledIntervalL2Operator P T
    (inner ℝ (P.intervalPointProblem.eigenbasis i) f • P.intervalPointProblem.eigenbasis i) = _
  calc
    _ = inner ℝ (P.intervalPointProblem.eigenbasis i) f •
        reflectedKilledIntervalL2Operator P T (P.intervalPointProblem.eigenbasis i) := map_smul _ _ _
    _ = inner ℝ (P.intervalPointProblem.eigenbasis i) f •
        (Real.exp (-i.1⁻¹ * T.val) • P.intervalPointProblem.eigenbasis i) :=
      congrArg (fun v : IntervalSobolevL2 0 P.length => inner ℝ (P.intervalPointProblem.eigenbasis i) f • v)
        (reflectedKilledIntervalL2Operator_eigenbasis P T i)
    _ = (inner ℝ (P.intervalPointProblem.eigenbasis i) f * Real.exp (-i.1⁻¹ * T.val)) •
        P.intervalPointProblem.eigenbasis i := smul_smul _ _ _
    _ = _ := congrArg (fun z : ℝ => z • P.intervalPointProblem.eigenbasis i)
      ((congrArg (fun z : ℝ => inner ℝ (P.intervalPointProblem.eigenbasis i) f * z) (hc i)).trans (mul_comm _ _))

theorem reflectedKilledIntervalL2Operator_eq_heat (P : SpectralProblem n) (T : ℝ≥0) :
    reflectedKilledIntervalL2Operator P T = P.intervalPointProblem.compactPositiveInverse.heatSemigroup T := by
  apply ContinuousLinearMap.ext
  intro f
  exact (reflectedKilledIntervalL2Operator_hasSum P T f).unique
    (P.intervalPointProblem.compactPositiveInverse.hasSum_heatSemigroup T f)

theorem reflectedKilledIntervalL2Operator_zero (P : SpectralProblem n) :
    reflectedKilledIntervalL2Operator P 0 = ContinuousLinearMap.id ℝ (IntervalSobolevL2 0 P.length) := by
  rw [reflectedKilledIntervalL2Operator_eq_heat]
  exact P.intervalPointProblem.compactPositiveInverse.heatSemigroup_zero

theorem reflectedKilledIntervalL2Operator_add (P : SpectralProblem n) (s t : ℝ≥0) :
    reflectedKilledIntervalL2Operator P (s + t) =
      (reflectedKilledIntervalL2Operator P s).comp (reflectedKilledIntervalL2Operator P t) := by
  simp only [reflectedKilledIntervalL2Operator_eq_heat]
  exact P.intervalPointProblem.compactPositiveInverse.heatSemigroup_add s t

theorem reflectedKilledIntervalL2Operator_strong_continuous (P : SpectralProblem n)
    (f : IntervalSobolevL2 0 P.length) : Continuous (fun T : ℝ≥0 => reflectedKilledIntervalL2Operator P T f) := by
  simpa only [reflectedKilledIntervalL2Operator_eq_heat] using
    P.intervalPointProblem.compactPositiveInverse.heatSemigroup_strong_continuous f

noncomputable def reflectedKilledIntervalCurve (P : SpectralProblem n)
    (f : IntervalSobolevL2 0 P.length) (t : ℝ) : IntervalSobolevL2 0 P.length :=
  reflectedKilledIntervalL2Operator P t.toNNReal f

theorem reflectedKilledIntervalCurve_eq_heatCurve (P : SpectralProblem n)
    (f : IntervalSobolevL2 0 P.length) : reflectedKilledIntervalCurve P f = P.intervalPointProblem.heatCurve f := by
  funext t
  exact congrArg (fun A : IntervalSobolevL2 0 P.length →L[ℝ] IntervalSobolevL2 0 P.length => A f)
    (reflectedKilledIntervalL2Operator_eq_heat P t.toNNReal)

theorem reflectedKilledInterval_generator_iff_graph (P : SpectralProblem n)
    (u f : IntervalSobolevL2 0 P.length) :
    HasDerivWithinAt (reflectedKilledIntervalCurve P u) (-f) (Ici 0) 0 ↔
      (u, f) ∈ P.intervalPointProblem.operator.graph := by
  rw [reflectedKilledIntervalCurve_eq_heatCurve]
  exact P.intervalPointProblem.heat_generator_iff_graph u f

theorem reflectedKilledInterval_generator_iff_physical (P : SpectralProblem n)
    (f : IntervalSobolevL2 0 P.length) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 P.length) :
    HasDerivWithinAt (reflectedKilledIntervalCurve P (ofEnergy hu P.length_pos).state) (-f) (Ici 0) 0 ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v 0 P.length →
        intervalPointForm P.diffusivity P.strength P.site 0 P.length u v =
          ∫ x in (0 : ℝ)..P.length, f x * v x := by
  rw [reflectedKilledIntervalCurve_eq_heatCurve]
  exact P.intervalPointProblem.heat_generator_iff_physical f hu

end TimeTraps.Probability
