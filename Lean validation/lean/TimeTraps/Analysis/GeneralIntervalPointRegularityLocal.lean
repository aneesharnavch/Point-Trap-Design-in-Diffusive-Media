module

public import TimeTraps.Analysis.GeneralIntervalPointRegularityWeak
public import TimeTraps.Analysis.IntervalPointRegularityData

@[expose] public section

/-! Local H2 regularity of the actual point-interaction solution for arbitrary
L2 forcing.  The interval is nondegenerate and has no contact in its open
interior; contacts at its endpoints do not affect this conclusion. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

theorem intervalSobolevL2_memLp_subinterval {l r : ℝ} (f : IntervalSobolevL2 l r) {a b : ℝ}
    (hl : l ≤ a) (hr : b ≤ r) : MemLp f 2 (volume.restrict (Ioo a b)) :=
  (Lp.memLp f).mono_measure (Measure.restrict_mono_set volume (Ioo_subset_Ioo hl hr))

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem IntervalPointProblem.weak_local_regularity (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x)
    {a b : ℝ} (hl : l ≤ a) (hlr : a < b) (hr : b ≤ r)
    (hsite : ∀ i, P.site i ∉ Ioo a b) :
    ∃ v : ℝ → ℝ, IntervalSlopeRegularity u v (fun x => -f x / P.diffusivity) a b := by
  have hu' : IntervalEnergy u a b := hu.mono (by
    rw [uIcc_of_le hlr.le, uIcc_of_le P.interval_pos.le]
    exact Icc_subset_Icc hl hr)
  have hf : MemLp (fun x => -f x / P.diffusivity) 2 (volume.restrict (Ioo a b)) := by
    simpa only [neg_mul, neg_div, div_eq_mul_inv, mul_comm, mul_neg] using
      (intervalSobolevL2_memLp_subinterval f hl hr).const_mul (-P.diffusivity⁻¹)
  have hd : MemLp (deriv u) 2 (volume.restrict (Ioo a b)) := by
    apply hu'.derivative_memLp.mono_measure
    rw [uIoc_of_le hlr.le]
    exact Measure.restrict_mono_set volume Ioo_subset_Ioc_self
  obtain ⟨v, hv, huv, hgv⟩ := (P.weak_slope_derivative f hweak hl hr hsite).energy_representative hlr
    (show IntegrableOn (deriv u) (Ioo a b) volume from hd.integrable (by norm_num)).locallyIntegrableOn hf
  exact ⟨v, hu', hv, huv, hgv.symm⟩

theorem IntervalPointProblem.operator_local_regularity (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hgraph : ((ofEnergy hu P.interval_pos).state, f) ∈ P.operator.graph)
    {a b : ℝ} (hl : l ≤ a) (hlr : a < b) (hr : b ≤ r)
    (hsite : ∀ i, P.site i ∉ Ioo a b) :
    ∃ v : ℝ → ℝ, IntervalSlopeRegularity u v (fun x => -f x / P.diffusivity) a b :=
  P.weak_local_regularity f hu ((P.operator_graph_iff_physical f hu).mp hgraph) hl hlr hr hsite

theorem IntervalPointProblem.solution_local_regularity (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {a b : ℝ} (hl : l ≤ a) (hlr : a < b) (hr : b ≤ r)
    (hsite : ∀ i, P.site i ∉ Ioo a b) :
    ∃ v : ℝ → ℝ, IntervalSlopeRegularity ((P.solution f).representative P.interval_pos) v
      (fun x => -f x / P.diffusivity) a b :=
  P.weak_local_regularity f ((P.solution f).representative_spec P.interval_pos).1
    (P.solution_physical f) hl hlr hr hsite

end TimeTraps.Analysis
