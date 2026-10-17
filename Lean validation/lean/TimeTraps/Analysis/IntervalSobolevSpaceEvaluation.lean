module

public import TimeTraps.Analysis.IntervalSobolevSpaceRepresentation

@[expose] public section

/-! Evaluation at every point of the closed interval, including both
endpoint traces, is a continuous linear functional on the actual bundled
Hilbert Sobolev space. Its value is the unique energy representative. -/

namespace TimeTraps.Analysis.IntervalSobolevSpace

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

theorem representative_add {l r : ℝ} (u v : IntervalSobolevSpace l r) (hlr : l < r) :
    EqOn ((u + v).representative hlr)
      (fun x => u.representative hlr x + v.representative hlr x) (Icc l r) := by
  apply (u + v).representative_unique hlr
  · change ContinuousOn (u.representative hlr + v.representative hlr) (Icc l r)
    have hu := (u.representative_spec hlr).1.continuousOn
    have hv := (v.representative_spec hlr).1.continuousOn
    simpa only [uIcc_of_le hlr.le] using hu.add hv
  · have hs : (u + v).state = u.state + v.state := (stateL l r).map_add u v
    rw [hs]
    exact (Lp.coeFn_add u.state v.state).trans
      ((u.representative_spec hlr).2.1.add (v.representative_spec hlr).2.1)

theorem representative_smul {l r : ℝ} (u : IntervalSobolevSpace l r) (hlr : l < r) (c : ℝ) :
    EqOn ((c • u).representative hlr) (fun x => c * u.representative hlr x) (Icc l r) := by
  apply (c • u).representative_unique hlr
  · change ContinuousOn ((fun _ => c) * u.representative hlr) (Icc l r)
    simpa only [uIcc_of_le hlr.le] using
      continuousOn_const.mul (u.representative_spec hlr).1.continuousOn
  · have hs : (c • u).state = c • u.state := (stateL l r).map_smul c u
    rw [hs]
    filter_upwards [Lp.coeFn_smul c u.state, (u.representative_spec hlr).2.1] with x hx hy
    simpa only [Pi.smul_apply, smul_eq_mul, hy] using hx

theorem representative_abs_le {l r x : ℝ} (u : IntervalSobolevSpace l r)
    (hlr : l < r) (hx : x ∈ Icc l r) :
    |u.representative hlr x| ≤ Real.sqrt (2 / (r - l) + 2 * (r - l)) * ‖u‖ := by
  have hL : 0 < r - l := sub_pos.mpr hlr
  have hI : 0 ≤ ∫ t in l..r, u.representative hlr t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hlr.le (fun t => sq_nonneg _)
  have hJ : 0 ≤ ∫ t in l..r, deriv (u.representative hlr) t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hlr.le (fun t => sq_nonneg _)
  have hA : 0 ≤ 2 / (r - l) := by positivity
  have hB : 0 ≤ 2 * (r - l) := by positivity
  have hb : u.representative hlr x ^ 2 ≤ (2 / (r - l) + 2 * (r - l)) * ‖u‖ ^ 2 := by
    calc
      _ ≤ (2 / (r - l)) * (∫ t in l..r, u.representative hlr t ^ 2) +
          2 * (r - l) * (∫ t in l..r, deriv (u.representative hlr) t ^ 2) :=
        (u.representative_spec hlr).1.trace_sq_le hlr hx
      _ ≤ _ := by
        rw [u.norm_sq_eq_h1SizeSq hlr]
        unfold intervalH1SizeSq
        nlinarith [mul_nonneg hA hJ, mul_nonneg hB hI]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (add_nonneg hA hB)]
  exact hb

def evalLinear {l r : ℝ} (hlr : l < r) (x : ℝ) (hx : x ∈ Icc l r) :
    IntervalSobolevSpace l r →ₗ[ℝ] ℝ where
  toFun u := u.representative hlr x
  map_add' u v := representative_add u v hlr hx
  map_smul' c u := by
    simpa only [smul_eq_mul, RingHom.id_apply] using representative_smul u hlr c hx

def evalL {l r : ℝ} (hlr : l < r) (x : ℝ) (hx : x ∈ Icc l r) :
    IntervalSobolevSpace l r →L[ℝ] ℝ :=
  (evalLinear hlr x hx).mkContinuous (Real.sqrt (2 / (r - l) + 2 * (r - l)))
    (fun u => by
      change ‖u.representative hlr x‖ ≤ _
      simpa only [Real.norm_eq_abs] using representative_abs_le u hlr hx)

theorem evalL_apply {l r : ℝ} (hlr : l < r) (x : ℝ) (hx : x ∈ Icc l r)
    (u : IntervalSobolevSpace l r) : evalL hlr x hx u = u.representative hlr x := rfl

theorem evalL_ofEnergy {v : ℝ → ℝ} {l r : ℝ} (hv : IntervalEnergy v l r)
    (hlr : l < r) (x : ℝ) (hx : x ∈ Icc l r) : evalL hlr x hx (ofEnergy hv hlr) = v x :=
  representative_ofEnergy hv hlr hx

theorem evalL_norm_le {l r : ℝ} (hlr : l < r) (x : ℝ) (hx : x ∈ Icc l r) :
    ‖evalL hlr x hx‖ ≤ Real.sqrt (2 / (r - l) + 2 * (r - l)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  simpa only [evalL_apply, Real.norm_eq_abs] using representative_abs_le u hlr hx

end

end TimeTraps.Analysis.IntervalSobolevSpace
