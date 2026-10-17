module

public import TimeTraps.Analysis.IntervalDirichletFormCoercive

@[expose] public section

/-! Actual zero-trace energy functions enter the full Dirichlet Hilbert
space, and the restricted bounded form is their physical integral pairing. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {l r : ℝ}

noncomputable def IntervalDirichletBoundary.ofEnergy (B : IntervalDirichletBoundary l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hzero : ∀ x ∈ B.zero_sites, u x = 0) :
    IntervalDirichletSpace B :=
  ⟨IntervalSobolevSpace.ofEnergy hu B.interval_pos,
    (B.subspace_mem_iff _).mpr fun x hx =>
      (representative_ofEnergy hu B.interval_pos (B.site_mem hx)).trans (hzero x hx)⟩

theorem IntervalDirichletBoundary.ofEnergy_state_ae (B : IntervalDirichletBoundary l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hzero : ∀ x ∈ B.zero_sites, u x = 0) :
    B.stateL (B.ofEnergy hu hzero) =ᵐ[volume.restrict (Ioo l r)] u :=
  (IntervalSobolevSpace.ofEnergy_spec hu B.interval_pos).1

theorem IntervalDirichletBoundary.ofEnergy_representative (B : IntervalDirichletBoundary l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hzero : ∀ x ∈ B.zero_sites, u x = 0) :
    EqOn ((B.ofEnergy hu hzero : IntervalSobolevSpace l r).representative B.interval_pos)
      u (Icc l r) := representative_ofEnergy hu B.interval_pos

theorem intervalDirichletPointForm_ofEnergy {ι : Type*} [Fintype ι]
    (B : IntervalDirichletBoundary l r) (D : ℝ) (κ z : ι → ℝ)
    (hz : ∀ i, z i ∈ Icc l r) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (huz : ∀ x ∈ B.zero_sites, u x = 0) (hvz : ∀ x ∈ B.zero_sites, v x = 0) :
    intervalDirichletPointForm B D κ z hz (B.ofEnergy hu huz) (B.ofEnergy hv hvz) =
      intervalPointForm D κ z l r u v := by
  rw [intervalDirichletPointForm_apply]
  exact intervalPointForm_congr D κ z B.interval_pos.le hz
    (B.ofEnergy_representative hu huz) (B.ofEnergy_representative hv hvz)

end TimeTraps.Analysis
