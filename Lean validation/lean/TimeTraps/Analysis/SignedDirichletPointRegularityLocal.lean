module

public import TimeTraps.Analysis.SignedDirichletPointRegularityWeak
public import TimeTraps.Analysis.GeneralIntervalPointRegularityLocal

@[expose] public section

/-! Local H2 regularity for the actual signed absorbing-boundary
operator graph under arbitrary L2 forcing. The certificate supplies an
AC/L2 slope, classical first derivatives in the interior, the second
derivative almost everywhere, and both one-sided slope traces. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedDirichletPointProblem.weak_local_regularity (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (hweak : ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x)
    {a b : ℝ} (hl : l ≤ a) (hlr : a < b) (hr : b ≤ r)
    (hsite : ∀ i, P.site i ∉ Ioo a b) :
    ∃ v : ℝ → ℝ, IntervalSlopeRegularity u v (fun x => -f x / P.diffusivity) a b := by
  have hu' : IntervalEnergy u a b := hu.mono (by
    rw [uIcc_of_le hlr.le, uIcc_of_le P.boundary.interval_pos.le]
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

theorem SignedDirichletPointProblem.operator_local_regularity (P : SignedDirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hgraph : (P.boundary.stateL (P.boundary.ofEnergy hu huz), f) ∈ P.operator.graph)
    {a b : ℝ} (hl : l ≤ a) (hlr : a < b) (hr : b ≤ r)
    (hsite : ∀ i, P.site i ∉ Ioo a b) :
    ∃ v : ℝ → ℝ, IntervalSlopeRegularity u v (fun x => -f x / P.diffusivity) a b :=
  P.weak_local_regularity f hu ((P.operator_graph_iff_physical f hu huz).mp hgraph) hl hlr hr hsite

end TimeTraps.Analysis
