module

public import TimeTraps.Analysis.IntervalSobolevSpace
public import TimeTraps.Analysis.IntervalEnergyTrace

@[expose] public section

/-! Identification of the bundled Hilbert graph with actual absolutely
continuous energy representatives. The Hilbert norm is exactly the H1
size formed from the state and its actual derivative. -/

namespace TimeTraps.Analysis.IntervalSobolevSpace

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

def stateL (l r : ℝ) : IntervalSobolevSpace l r →L[ℝ] IntervalSobolevL2 l r :=
  (WithLp.fstL 2 ℝ _ _).comp (intervalSobolevGraph l r).subtypeL

def gradientL (l r : ℝ) : IntervalSobolevSpace l r →L[ℝ] IntervalSobolevL2 l r :=
  (WithLp.sndL 2 ℝ _ _).comp (intervalSobolevGraph l r).subtypeL

theorem energy_representative {l r : ℝ} (u : IntervalSobolevSpace l r) (hlr : l < r) :
    ∃ v : ℝ → ℝ, IntervalEnergy v l r ∧
      u.state =ᵐ[volume.restrict (Ioo l r)] v ∧
      u.gradient =ᵐ[volume.restrict (Ioo l r)] deriv v :=
  u.weakDerivative.energy_representative hlr
    (show IntegrableOn u.state (Ioo l r) volume from
      (Lp.memLp u.state).integrable (by norm_num)).locallyIntegrableOn (Lp.memLp u.gradient)

def representative {l r : ℝ} (u : IntervalSobolevSpace l r) (hlr : l < r) : ℝ → ℝ :=
  Classical.choose (u.energy_representative hlr)

theorem representative_spec {l r : ℝ} (u : IntervalSobolevSpace l r) (hlr : l < r) :
    IntervalEnergy (u.representative hlr) l r ∧
      u.state =ᵐ[volume.restrict (Ioo l r)] u.representative hlr ∧
      u.gradient =ᵐ[volume.restrict (Ioo l r)] deriv (u.representative hlr) :=
  Classical.choose_spec (u.energy_representative hlr)

theorem representative_unique {l r : ℝ} (u : IntervalSobolevSpace l r) (hlr : l < r)
    {v : ℝ → ℝ} (hv : ContinuousOn v (Icc l r))
    (huv : u.state =ᵐ[volume.restrict (Ioo l r)] v) :
    EqOn (u.representative hlr) v (Icc l r) := by
  have h := (u.representative_spec hlr).2.1.symm.trans huv
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at h
  exact Measure.eqOn_Icc_of_ae_eq volume hlr.ne h
    (by simpa only [uIcc_of_le hlr.le] using (u.representative_spec hlr).1.continuousOn) hv

theorem norm_sq_eq_h1SizeSq {l r : ℝ} (u : IntervalSobolevSpace l r) (hlr : l < r) :
    ‖u‖ ^ 2 = intervalH1SizeSq (u.representative hlr) l r := by
  rw [u.norm_sq]
  unfold intervalH1SizeSq
  simp only [intervalIntegral.integral_of_le hlr.le, integral_Ioc_eq_integral_Ioo]
  congr 1
  · apply integral_congr_ae
    filter_upwards [(u.representative_spec hlr).2.1] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [(u.representative_spec hlr).2.2] with x hx
    rw [hx]

theorem norm_eq_h1Size {l r : ℝ} (u : IntervalSobolevSpace l r) (hlr : l < r) :
    ‖u‖ = intervalH1Size (u.representative hlr) l r := by
  unfold intervalH1Size
  rw [← u.norm_sq_eq_h1SizeSq hlr, Real.sqrt_sq (norm_nonneg u)]

def ofEnergy {v : ℝ → ℝ} {l r : ℝ} (hv : IntervalEnergy v l r) (hlr : l < r) :
    IntervalSobolevSpace l r := by
  have hs := (hv.sobolev hlr.le).1
  have hg : MemLp (deriv v) 2 (volume.restrict (Ioo l r)) := by
    apply hv.derivative_memLp.mono_measure
    rw [uIoc_of_le hlr.le]
    exact Measure.restrict_mono_set volume Ioo_subset_Ioc_self
  refine ⟨WithLp.toLp 2 (hs.toLp v, hg.toLp (deriv v)), ?_⟩
  apply (intervalSobolevGraph_mem_iff _).mpr
  exact (hv.weakDerivative hlr.le).congr_ae hs.coeFn_toLp.symm hg.coeFn_toLp.symm

theorem ofEnergy_spec {v : ℝ → ℝ} {l r : ℝ} (hv : IntervalEnergy v l r) (hlr : l < r) :
    (ofEnergy hv hlr).state =ᵐ[volume.restrict (Ioo l r)] v ∧
      (ofEnergy hv hlr).gradient =ᵐ[volume.restrict (Ioo l r)] deriv v := by
  constructor
  · exact (hv.sobolev hlr.le).1.coeFn_toLp
  · have hg : MemLp (deriv v) 2 (volume.restrict (Ioo l r)) := by
      apply hv.derivative_memLp.mono_measure
      rw [uIoc_of_le hlr.le]
      exact Measure.restrict_mono_set volume Ioo_subset_Ioc_self
    exact hg.coeFn_toLp

theorem representative_ofEnergy {v : ℝ → ℝ} {l r : ℝ}
    (hv : IntervalEnergy v l r) (hlr : l < r) :
    EqOn ((ofEnergy hv hlr).representative hlr) v (Icc l r) :=
  (ofEnergy hv hlr).representative_unique hlr
    (by simpa only [uIcc_of_le hlr.le] using hv.continuousOn) (ofEnergy_spec hv hlr).1

theorem ext_state {l r : ℝ} {u v : IntervalSobolevSpace l r}
    (huv : u.state = v.state) : u = v := by
  have hd : u.gradient =ᵐ[volume.restrict (Ioo l r)] v.gradient :=
    u.weakDerivative.unique (huv ▸ v.weakDerivative)
      (show IntegrableOn u.gradient (Ioo l r) volume from
        (Lp.memLp u.gradient).integrable (by norm_num)).locallyIntegrableOn
      (show IntegrableOn v.gradient (Ioo l r) volume from
        (Lp.memLp v.gradient).integrable (by norm_num)).locallyIntegrableOn
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext huv (Lp.ext hd)

end

end TimeTraps.Analysis.IntervalSobolevSpace
