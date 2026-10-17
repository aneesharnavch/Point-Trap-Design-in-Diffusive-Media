module

public import TimeTraps.Analysis.IntervalSobolevSpaceRepresentation
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

@[expose] public section

/-! Density of the actual Sobolev state range in L2. Every smooth test
belongs to the range; the full test-function fundamental lemma shows that
the orthogonal complement vanishes. This is distinct from injectivity of
the state map. -/

namespace TimeTraps.Analysis.IntervalSobolevSpace

open Set MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace

theorem stateL_smooth_mem_range {l r : ℝ} (hlr : l < r) {φ : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ φ) (hp : MemLp φ 2 (volume.restrict (Ioo l r))) :
    hp.toLp φ ∈ (stateL l r).range := by
  have hφ : IntervalEnergy φ l r := intervalEnergy_of_continuous_derivative hlr.le
    hc.continuous.continuousOn (hc.continuous_deriv (by simp)).continuousOn
    (fun x _ => (hc.differentiable (by simp) x).hasDerivAt)
  refine ⟨ofEnergy hφ hlr, ?_⟩
  apply Lp.ext
  exact (ofEnergy_spec hφ hlr).1.trans hp.coeFn_toLp.symm

theorem stateL_orthogonal_zero {l r : ℝ} (hlr : l < r) (f : IntervalSobolevL2 l r)
    (hf : ∀ u : IntervalSobolevSpace l r, ⟪stateL l r u, f⟫_ℝ = 0) : f = 0 := by
  have hz : ∀ᵐ x, x ∈ Ioo l r → f x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (show IntegrableOn f (Ioo l r) volume from
        (Lp.memLp f).integrable (by norm_num)).locallyIntegrableOn
    intro φ hc hk hs
    have hp : MemLp φ 2 (volume.restrict (Ioo l r)) :=
      hc.continuous.memLp_of_hasCompactSupport hk
    obtain ⟨u, hu⟩ := stateL_smooth_mem_range hlr hc hp
    change stateL l r u = hp.toLp φ at hu
    have he := hf u
    rw [hu, intervalSobolevL2_test_pairing f hp hs] at he
    simpa only [smul_eq_mul, mul_comm] using he
  apply Lp.ext
  apply EventuallyEq.trans _ (Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo l r))).symm
  exact (ae_restrict_iff' measurableSet_Ioo).mpr hz

theorem stateL_denseRange {l r : ℝ} (hlr : l < r) : DenseRange (stateL l r) := by
  let K : Submodule ℝ (IntervalSobolevL2 l r) := (stateL l r).range
  have hk : Kᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    apply stateL_orthogonal_zero hlr f
    intro u
    exact (K.mem_orthogonal f).mp hf (stateL l r u) ⟨u, rfl⟩
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, hk, Submodule.bot_orthogonal_eq_top]
  change Dense (K : Set (IntervalSobolevL2 l r))
  rw [dense_iff_closure_eq]
  exact congrArg (fun S : Submodule ℝ (IntervalSobolevL2 l r) => (S : Set (IntervalSobolevL2 l r))) hclosure

end TimeTraps.Analysis.IntervalSobolevSpace
