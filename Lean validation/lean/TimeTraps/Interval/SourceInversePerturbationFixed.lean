module

public import TimeTraps.Interval.SourceInversePerturbationComposition

@[expose] public section

/-! The fixed-density qualification in the source perturbation theorem.
Positive continuity alone gives the physical first derivative and a
little-o remainder. No C1 density hypothesis or quadratic remainder is
silently included. -/

namespace TimeTraps.Interval

open Set Filter TimeTraps.Analysis
open scoped Topology

theorem source_fixed_density_physical_derivative (P : SourceInterval) (hmass : P.mass = 1)
    {q : ℝ → ℝ} {v : ℝ} (hq : HasDerivAt q v 0) (hq₀ : q 0 ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ε => P.inverse (q ε)) (v / P.density (P.inverse (q 0))) 0 := by
  have hd := (P.inverse_derivative hq₀).comp 0 hq
  convert! hd using 1
  rw [hmass]
  ring

theorem source_fixed_density_physical_littleO (P : SourceInterval) (hmass : P.mass = 1)
    {q : ℝ → ℝ} {v : ℝ} (hq : HasDerivAt q v 0) (hq₀ : q 0 ∈ Ioo (0 : ℝ) 1) :
    (fun ε => P.inverse (q ε) - P.inverse (q 0) -
      ε * (v / P.density (P.inverse (q 0)))) =o[𝓝 (0 : ℝ)] (fun ε => ε) := by
  have hd := source_fixed_density_physical_derivative P hmass hq hq₀
  simpa only [sub_zero, smul_eq_mul] using hd.isLittleO

end TimeTraps.Interval
