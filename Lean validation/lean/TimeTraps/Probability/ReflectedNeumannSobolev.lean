module

public import TimeTraps.Probability.ReflectedNeumannGeneratorGraph

@[expose] public section

/-! The full physical reflected-L2 generator has the genuine one-dimensional
Neumann H2 domain: an AC state with an AC/L2 slope, whose two endpoint
traces vanish. Its action is D times the actual weak second derivative.
The characterization uses actual representatives and Lebesgue weak
derivatives, not a spectral definition of the Sobolev space. -/

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

theorem reflectedPhysical_generator_iff_neumann_sobolev (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f g : ReflectedUniformL2 L hL) :
    HasDerivWithinAt (reflectedGaussianPhysicalL2Curve L hL D f) g (Ici 0) 0 ↔
      ∃ U j : ℝ → ℝ, f =ᵐ[reflectedUniformLaw L hL] U ∧
        IntervalSlopeRegularity U j (fun x => g x / D) 0 L ∧ j 0 = 0 ∧ j L = 0 := by
  have hforce : (fun x : ℝ =>
      -((-reflectedUniformL2Equiv L hL g : IntervalSobolevL2 0 L) x) / D) =ᵐ[
        volume.restrict (Ioo 0 L)] (fun x => g x / D) := by
    filter_upwards [Lp.coeFn_neg (reflectedUniformL2Equiv L hL g),
      reflectedUniformL2Equiv_coe L hL g] with x hn hx
    rw [hn]
    simp only [Pi.neg_apply, neg_neg]
    rw [hx]
  rw [reflectedPhysical_generator_iff_neumann_graph L hL D hD f g,
    reflectedNeumann_operator_graph_iff L hL D hD]
  constructor
  · rintro ⟨U, j, hu, hj, hleft, hright⟩
    refine ⟨U, j, (reflectedUniformLaw_ae_iff L hL _).mpr
      ((reflectedUniformL2Equiv_coe L hL f).symm.trans hu), ?_, hleft, hright⟩
    exact ⟨hj.state_energy, hj.slope_energy, hj.slope_ae, hj.second_ae.trans hforce⟩
  · rintro ⟨U, j, hu, hj, hleft, hright⟩
    refine ⟨U, j, (reflectedUniformL2Equiv_coe L hL f).trans
      ((reflectedUniformLaw_ae_iff L hL _).mp hu), ?_, hleft, hright⟩
    exact ⟨hj.state_energy, hj.slope_energy, hj.slope_ae, hj.second_ae.trans hforce.symm⟩

theorem reflectedPhysical_generator_domain_iff_neumann_sobolev (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f : ReflectedUniformL2 L hL) :
    DifferentiableWithinAt ℝ (reflectedGaussianPhysicalL2Curve L hL D f) (Ici 0) 0 ↔
      ∃ U j : ℝ → ℝ, f =ᵐ[reflectedUniformLaw L hL] U ∧
        IntervalEnergy U 0 L ∧ IntervalEnergy j 0 L ∧
        deriv U =ᵐ[volume.restrict (Ioo 0 L)] j ∧ j 0 = 0 ∧ j L = 0 := by
  constructor
  · intro hf
    obtain ⟨U, j, hu, hj, hleft, hright⟩ :=
      (reflectedPhysical_generator_iff_neumann_sobolev L hL D hD f _).mp hf.hasDerivWithinAt
    exact ⟨U, j, hu, hj.state_energy, hj.slope_energy, hj.slope_ae, hleft, hright⟩
  · rintro ⟨U, j, hu, hU, hj, hUj, hleft, hright⟩
    have hd : MemLp (deriv j) 2 (volume.restrict (Ioo 0 L)) :=
      MemLp.ae_eq (IntervalSobolevSpace.ofEnergy_spec hj hL).2
        (Lp.memLp (IntervalSobolevSpace.ofEnergy hj hL).gradient)
    let G : IntervalSobolevL2 0 L := (hd.const_mul D).toLp (fun x => D * deriv j x)
    let g : ReflectedUniformL2 L hL := (reflectedUniformL2Equiv L hL).symm G
    have hg : g =ᵐ[volume.restrict (Ioo 0 L)] (fun x => D * deriv j x) :=
      Filter.EventuallyEq.trans ((reflectedUniformLaw_ae_iff L hL _).mp
        (reflectedUniformL2Equiv_symm_coe L hL G)) (hd.const_mul D).coeFn_toLp
    apply HasDerivWithinAt.differentiableWithinAt (f' := g)
    apply (reflectedPhysical_generator_iff_neumann_sobolev L hL D hD f g).mpr
    refine ⟨U, j, hu, ⟨hU, hj, hUj, ?_⟩, hleft, hright⟩
    filter_upwards [hg] with x hx
    rw [hx]
    field_simp [hD.ne']

end TimeTraps.Probability
