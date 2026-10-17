module

public import TimeTraps.Analysis.IntervalSobolevUniqueness

@[expose] public section

/-! The primitive of an arbitrary L2 function on a finite interval is an
energy state with that distributional weak derivative. No continuity of
the prescribed derivative is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter

theorem intervalSobolev_primitive {g : ℝ → ℝ} {l r : ℝ} (hlr : l ≤ r)
    (hg : MemLp g 2 (volume.restrict (Ioo l r))) :
    IntervalEnergy (fun x => ∫ t in l..x, g t) l r ∧
      IntervalWeakDerivative (fun x => ∫ t in l..x, g t) g l r := by
  have hi : IntervalIntegrable g volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr).mpr (hg.integrable (by norm_num))
  have hac := hi.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : l ∈ uIcc l r)
  have hd : deriv (fun x => ∫ t in l..x, g t) =ᵐ[volume.restrict (Ioo l r)] g := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hi.ae_hasDerivAt_integral] with x hx
    intro hm
    exact (hx (by simpa only [uIcc_of_le hlr] using Ioo_subset_Icc_self hm)
      l left_mem_uIcc).deriv
  have he : IntervalEnergy (fun x => ∫ t in l..x, g t) l r := by
    refine ⟨hac, (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr).mpr ?_⟩
    apply hg.integrable_sq.congr
    filter_upwards [hd] with x hx
    rw [hx]
  exact ⟨he, (he.weakDerivative hlr).congr_ae Filter.EventuallyEq.rfl hd⟩

end TimeTraps.Analysis
