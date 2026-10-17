module

public import TimeTraps.Analysis.IntervalPointRegularityWeak
public import TimeTraps.Analysis.IntervalPointRegularityData

@[expose] public section

/-! Local H2 regularity of the actual point-interaction solution for arbitrary
L2 forcing.  The interval is nondegenerate and has no contact in its open
interior; contacts at its endpoints do not affect this conclusion. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

theorem unitIntervalL2_memLp_subinterval (f : UnitIntervalL2) {l r : ℝ}
    (hl : 0 ≤ l) (hr : r ≤ 1) : MemLp f 2 (volume.restrict (Ioo l r)) :=
  (Lp.memLp f).mono_measure (Measure.restrict_mono_set volume (Ioo_subset_Ioo hl hr))

variable {ι : Type*} [Fintype ι]

theorem UnitPointProblem.weak_local_regularity (P : UnitPointProblem ι)
    (f : UnitIntervalL2) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1)
    (hweak : ∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
      unitPointForm P.diffusivity P.strength P.site u v = ∫ x in (0 : ℝ)..1, f x * v x)
    {l r : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hr : r ≤ 1)
    (hsite : ∀ i, P.site i ∉ Ioo l r) :
    ∃ v : ℝ → ℝ, IntervalSlopeRegularity u v (fun x => -f x / P.diffusivity) l r := by
  have hu' : IntervalEnergy u l r := hu.mono (by
    rw [uIcc_of_le hlr.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hl hr)
  have hf : MemLp (fun x => -f x / P.diffusivity) 2 (volume.restrict (Ioo l r)) := by
    simpa only [neg_mul, neg_div, div_eq_mul_inv, mul_comm, mul_neg] using
      (unitIntervalL2_memLp_subinterval f hl hr).const_mul (-P.diffusivity⁻¹)
  have hd : MemLp (deriv u) 2 (volume.restrict (Ioo l r)) := by
    apply hu'.derivative_memLp.mono_measure
    rw [uIoc_of_le hlr.le]
    exact Measure.restrict_mono_set volume Ioo_subset_Ioc_self
  obtain ⟨v, hv, huv, hgv⟩ := (P.weak_slope_derivative f hweak hl hr hsite).energy_representative hlr
    (show IntegrableOn (deriv u) (Ioo l r) volume from hd.integrable (by norm_num)).locallyIntegrableOn hf
  exact ⟨v, hu', hv, huv, hgv.symm⟩

theorem UnitPointProblem.operator_local_regularity (P : UnitPointProblem ι)
    (f : UnitIntervalL2) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1)
    (hgraph : ((ofEnergy hu zero_lt_one).state, f) ∈ P.operator.graph)
    {l r : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hr : r ≤ 1)
    (hsite : ∀ i, P.site i ∉ Ioo l r) :
    ∃ v : ℝ → ℝ, IntervalSlopeRegularity u v (fun x => -f x / P.diffusivity) l r :=
  P.weak_local_regularity f hu ((P.operator_graph_iff_physical f hu).mp hgraph) hl hlr hr hsite

theorem UnitPointProblem.solution_local_regularity (P : UnitPointProblem ι)
    (f : UnitIntervalL2) {l r : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hr : r ≤ 1)
    (hsite : ∀ i, P.site i ∉ Ioo l r) :
    ∃ v : ℝ → ℝ, IntervalSlopeRegularity ((P.solution f).representative zero_lt_one) v
      (fun x => -f x / P.diffusivity) l r :=
  P.weak_local_regularity f ((P.solution f).representative_spec zero_lt_one).1
    (P.solution_physical f) hl hlr hr hsite

end TimeTraps.Analysis
