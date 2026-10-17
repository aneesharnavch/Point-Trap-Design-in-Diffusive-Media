module

public import TimeTraps.Probability.ReflectedFellerLaplace
public import TimeTraps.Probability.ReflectedNeumannLaplaceElliptic
public import TimeTraps.Probability.ReflectedFellerDomainIdentification

@[expose] public section

/-! Continuous forcing upgrades the actual L2 resolvent's AC slope to
a classical continuous second derivative. The continuous Laplace integral
is therefore a genuine C² Neumann solution of alpha*U-D*U''=f, and belongs
to the actual uniform-norm generator domain. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

theorem reflectedFellerLaplace_neumannC2 (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) {α : ℝ} (hα : 0 < α)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    ∃ F : ReflectedNeumannC2 L, F.valueMap = reflectedFellerLaplace L hL D α f ∧
      α • F.valueMap - D • F.curvatureMap = f := by
  obtain ⟨U, j, hu, hj, hleft, hright⟩ :=
    reflectedNeumannLaplace_elliptic_strong L hL D hD hα (reflectedFellerToL2 L hL f)
  have hUc : ContinuousOn U (Icc 0 L) := by
    simpa only [uIcc_of_le hL.le] using hj.state_energy.continuousOn
  have hjc : ContinuousOn j (Icc 0 L) := by
    simpa only [uIcc_of_le hL.le] using hj.slope_energy.continuousOn
  let q : ℝ → ℝ := fun x => (α * U x - reflectedFellerExtension L hL f x) / D
  have hqc : ContinuousOn q (Icc 0 L) :=
    ((continuousOn_const.mul hUc).sub
      (reflectedFellerExtension L hL f).continuous.continuousOn).div_const D
  have hjq : deriv j =ᵐ[volume.restrict (Ioo 0 L)] q := by
    filter_upwards [hj.second_ae, (reflectedUniformLaw_ae_iff L hL _).mp
      (reflectedFellerToL2_coe L hL f)] with x hx hf
    rw [hx, hf]
  let F : ReflectedNeumannC2 L :=
    { value := U
      slope := j
      curvature := q
      value_continuous := hUc
      slope_continuous := hjc
      curvature_continuous := hqc
      value_derivative := fun _ hx => hj.hasDerivAt hx
      slope_derivative := fun _ hx => intervalEnergy_hasDerivAt_of_ae_deriv hj.slope_energy hqc hjq hx
      neumann_left := hleft
      neumann_right := hright }
  have he : reflectedFellerExtension L hL (reflectedFellerLaplace L hL D α f)
      =ᵐ[reflectedUniformLaw L hL] U := by
    have he' := reflectedFellerToL2_coe L hL (reflectedFellerLaplace L hL D α f)
    rw [reflectedFellerLaplace_toL2 L hL D hα f] at he'
    exact he'.symm.trans hu
  have hecc : reflectedFellerExtension L hL (reflectedFellerLaplace L hL D α f)
      =ᵐ[volume.restrict (Icc 0 L)] U := by
    have he' := (reflectedUniformLaw_ae_iff L hL _).mp he
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at he'
  have hepoint := Measure.eqOn_Icc_of_ae_eq volume hL.ne hecc
    (reflectedFellerExtension L hL (reflectedFellerLaplace L hL D α f)).continuous.continuousOn hUc
  refine ⟨F, ?_, ?_⟩
  · ext x
    exact (reflectedFellerExtension_on_interval L hL _ x).symm.trans (hepoint x.property) |>.symm
  · ext x
    change α * U x.val - D * ((α * U x.val - reflectedFellerExtension L hL f x.val) / D) = f x
    rw [reflectedFellerExtension_on_interval L hL f x]
    field_simp
    ring

theorem reflectedFellerLaplace_generator (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) {α : ℝ} (hα : 0 < α)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t
      (reflectedFellerLaplace L hL D α f))
      (α • reflectedFellerLaplace L hL D α f - f) (Ici 0) 0 := by
  obtain ⟨F, hF, he⟩ := reflectedFellerLaplace_neumannC2 L hL D hD hα f
  have hcurv : D • F.curvatureMap = α • reflectedFellerLaplace L hL D α f - f := by
    rw [hF] at he
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp he).symm
  simpa only [hF, hcurv] using F.feller_generator hL D hD.le

end TimeTraps.Probability

end
