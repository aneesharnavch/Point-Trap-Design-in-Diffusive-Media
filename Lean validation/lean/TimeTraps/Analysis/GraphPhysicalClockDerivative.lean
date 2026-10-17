module

public import TimeTraps.Analysis.GraphPhysicalClockRegularity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section

/-! The genuine Borel-speed integral has its original rate as derivative
almost everywhere. This is derived by Lebesgue differentiation from the
proved bounded integrability, without any vertex continuity premise. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped NNReal Topology

theorem GraphPhysicalClockSpeed.rate_locallyIntegrable (v : GraphPhysicalClockSpeed) :
    LocallyIntegrable (fun r : ℝ => v.rate r.toNNReal) volume := by
  intro x
  exact ⟨Ioc (x - 1) (x + 1), Ioc_mem_nhds (by linarith) (by linarith),
    (v.rate_intervalIntegrable (x - 1) (x + 1)).1⟩

theorem GraphPhysicalClockSpeed.clock_hasDerivAt_ae (v : GraphPhysicalClockSpeed) :
    ∀ᵐ x : ℝ, HasDerivAt (fun t : ℝ => ∫ r in (0 : ℝ)..t, v.rate r.toNNReal) (v.rate x.toNNReal) x :=
  (_root_.LocallyIntegrable.ae_hasDerivAt_integral v.rate_locallyIntegrable).mono (fun _ hx => hx 0)

end TimeTraps.Analysis
