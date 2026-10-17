module

public import TimeTraps.Analysis.IntervalPeriodicSpace
public import TimeTraps.Analysis.IntervalSobolevDense

@[expose] public section

/-! Smooth functions supported inside the interval have matching endpoint
traces. Their inclusion in the actual periodic Sobolev space proves that
its state range is dense in the original interval L2 space. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter IntervalSobolevSpace
open scoped Topology ContDiff InnerProductSpace

variable {l r : ℝ}

theorem IntervalPeriodicBoundary.stateL_smooth_mem_range
    (B : IntervalPeriodicBoundary l r) {φ : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ φ) (hp : MemLp φ 2 (volume.restrict (Ioo l r)))
    (hs : tsupport φ ⊆ Ioo l r) : hp.toLp φ ∈ B.stateL.range := by
  obtain ⟨u, hu⟩ := IntervalSobolevSpace.stateL_smooth_mem_range B.interval_pos hc hp
  change u.state = hp.toLp φ at hu
  have hrep : EqOn (u.representative B.interval_pos) φ (Icc l r) :=
    u.representative_unique B.interval_pos hc.continuous.continuousOn (hu ▸ hp.coeFn_toLp)
  have hzero : ∀ x, x ∉ Ioo l r → φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hs (subset_closure hn))
  have hmem : u ∈ B.subspace := by
    apply (B.subspace_mem_iff u).mpr
    rw [hrep ⟨B.interval_pos.le, le_rfl⟩, hrep ⟨le_rfl, B.interval_pos.le⟩,
      hzero r (by simp), hzero l (by simp)]
  exact ⟨⟨u, hmem⟩, hu⟩

theorem IntervalPeriodicBoundary.stateL_orthogonal_zero
    (B : IntervalPeriodicBoundary l r) (f : IntervalSobolevL2 l r)
    (hf : ∀ u : IntervalPeriodicSpace B, ⟪B.stateL u, f⟫_ℝ = 0) : f = 0 := by
  have hz : ∀ᵐ x, x ∈ Ioo l r → f x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (show IntegrableOn f (Ioo l r) volume from
        (Lp.memLp f).integrable (by norm_num)).locallyIntegrableOn
    intro φ hc hk hs
    have hp : MemLp φ 2 (volume.restrict (Ioo l r)) :=
      hc.continuous.memLp_of_hasCompactSupport hk
    obtain ⟨u, hu⟩ := B.stateL_smooth_mem_range hc hp hs
    change B.stateL u = hp.toLp φ at hu
    have he := hf u
    rw [hu, intervalSobolevL2_test_pairing f hp hs] at he
    simpa only [smul_eq_mul, mul_comm] using he
  apply Lp.ext
  apply EventuallyEq.trans _ (Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo l r))).symm
  exact (ae_restrict_iff' measurableSet_Ioo).mpr hz

theorem IntervalPeriodicBoundary.stateL_denseRange (B : IntervalPeriodicBoundary l r) :
    DenseRange B.stateL := by
  let K : Submodule ℝ (IntervalSobolevL2 l r) := B.stateL.range
  have hk : Kᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    apply B.stateL_orthogonal_zero f
    intro u
    exact (K.mem_orthogonal f).mp hf (B.stateL u) ⟨u, rfl⟩
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, hk, Submodule.bot_orthogonal_eq_top]
  change Dense (K : Set (IntervalSobolevL2 l r))
  rw [dense_iff_closure_eq]
  exact congrArg (fun S : Submodule ℝ (IntervalSobolevL2 l r) =>
    (S : Set (IntervalSobolevL2 l r))) hclosure

end TimeTraps.Analysis
