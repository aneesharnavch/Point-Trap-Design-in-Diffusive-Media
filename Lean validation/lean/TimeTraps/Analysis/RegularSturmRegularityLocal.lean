module

public import TimeTraps.Analysis.RegularSturmRegularityWeak
public import TimeTraps.Analysis.IntervalFluxRegularity

@[expose] public section

/-! Every weak regular Sturm state under arbitrary Hilbert L2 forcing
has an actual AC/L2 physical flux on each contact-free closed cell. This
uses the distributional equation, not a regularity assumption on a state. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.weak_local_regularity (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u v =
        ∫ x in l..r, f x * Real.sqrt (P.speed x) * v x)
    {a b : ℝ} (hl : l ≤ a) (hab : a < b) (hr : b ≤ r)
    (hsite : ∀ i, P.site i ∉ Ioo a b) :
    ∃ j : ℝ → ℝ, IntervalFluxRegularity u j
      (fun x => P.potential x * u x - f x * Real.sqrt (P.speed x)) P.conductance a b := by
  have hm : volume.restrict (Ioo a b) ≤ volume.restrict (Ioo l r) :=
    Measure.restrict_mono_set volume (Ioo_subset_Ioo hl hr)
  have hu' : IntervalEnergy u a b := hu.mono (by
    rw [uIcc_of_le hab.le, uIcc_of_le P.boundary.interval_pos.le]
    exact Icc_subset_Icc hl hr)
  have hg := (P.fluxSource_memLp f hu).mono_measure hm
  have hj := (hu.weighted_derivative_memLp P.boundary.interval_pos.le
    P.conductance P.conductance_continuous).mono_measure hm
  obtain ⟨j, hje, hae, hge⟩ := (P.weak_flux_derivative f hu hweak hl hr hsite).energy_representative hab
    (show IntegrableOn (fun x => P.conductance x * deriv u x) (Ioo a b) volume from
      hj.integrable (by norm_num)).locallyIntegrableOn hg
  exact ⟨j, hu', hje, hae, hge.symm⟩

theorem RegularSturmProblem.operator_local_regularity (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hgraph : (P.stateL (P.boundary.ofEnergy hu huz), f) ∈ P.operator.graph)
    {a b : ℝ} (hl : l ≤ a) (hab : a < b) (hr : b ≤ r)
    (hsite : ∀ i, P.site i ∉ Ioo a b) :
    ∃ j : ℝ → ℝ, IntervalFluxRegularity u j
      (fun x => P.potential x * u x - f x * Real.sqrt (P.speed x)) P.conductance a b :=
  P.weak_local_regularity f hu ((P.operator_graph_iff_physical f hu huz).mp hgraph) hl hab hr hsite

end TimeTraps.Analysis
