module

public import TimeTraps.Analysis.IntervalSobolevConstant
public import TimeTraps.Analysis.IntervalSobolevPrimitive
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-! Equivalence of the full distributional H1 definition and an absolutely
continuous representative with L2 derivative on a nondegenerate finite
interval. The representative is unique on the closed interval, including
its endpoint traces; arbitrary null-set modifications are allowed in the
distributional class. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter

theorem IntervalWeakDerivative.energy_representative {u g : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (hu : IntervalWeakDerivative u g l r)
    (hui : LocallyIntegrableOn u (Ioo l r))
    (hg : MemLp g 2 (volume.restrict (Ioo l r))) :
    ∃ v : ℝ → ℝ, IntervalEnergy v l r ∧
      u =ᵐ[volume.restrict (Ioo l r)] v ∧
      g =ᵐ[volume.restrict (Ioo l r)] deriv v := by
  let V : ℝ → ℝ := fun x => ∫ t in l..x, g t
  obtain ⟨hVe, hVw⟩ := intervalSobolev_primitive hlr.le hg
  have hVi : LocallyIntegrableOn V (Ioo l r) :=
    (show IntegrableOn V (Ioo l r) volume from
      (hVe.sobolev hlr.le).1.integrable (by norm_num)).locallyIntegrableOn
  obtain ⟨c, hc⟩ := (hu.sub_same hVw hui hVi).ae_constant hlr (hui.sub hVi)
  let v : ℝ → ℝ := fun x => V x - (-c)
  have hv : IntervalEnergy v l r := hVe.sub (IntervalEnergy.const (-c) l r)
  have huv : u =ᵐ[volume.restrict (Ioo l r)] v := by
    filter_upwards [hc] with x hx
    change u x - V x = c at hx
    change u x = V x - (-c)
    linarith
  refine ⟨v, hv, huv, ?_⟩
  exact (hv.weakDerivative_iff hlr.le hg).mp (hu.congr_ae huv EventuallyEq.rfl)

theorem intervalSobolev_iff_energy_representative {u : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) : IntervalSobolev u l r ↔
      ∃ v : ℝ → ℝ, IntervalEnergy v l r ∧ u =ᵐ[volume.restrict (Ioo l r)] v := by
  constructor
  · rintro ⟨hui, g, hg, hu⟩
    obtain ⟨v, hv, huv, _⟩ := hu.energy_representative hlr
      (show IntegrableOn u (Ioo l r) volume from hui.integrable (by norm_num)).locallyIntegrableOn hg
    exact ⟨v, hv, huv⟩
  · rintro ⟨v, hv, huv⟩
    exact (hv.sobolev hlr.le).congr_ae huv.symm

theorem IntervalEnergy.representative_unique {u v : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (huv : u =ᵐ[volume.restrict (Ioo l r)] v) : EqOn u v (Icc l r) := by
  have hcc : u =ᵐ[volume.restrict (Icc l r)] v := by
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at huv
  exact Measure.eqOn_Icc_of_ae_eq volume hlr.ne hcc
    (by simpa only [uIcc_of_le hlr.le] using hu.continuousOn)
    (by simpa only [uIcc_of_le hlr.le] using hv.continuousOn)

end TimeTraps.Analysis
