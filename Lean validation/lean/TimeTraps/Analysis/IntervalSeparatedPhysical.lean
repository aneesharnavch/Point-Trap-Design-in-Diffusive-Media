module

public import TimeTraps.Analysis.IntervalSeparatedSpace
public import TimeTraps.Analysis.IntervalSobolevSpacePairing

@[expose] public section

/-! Actual energy functions with the selected zero endpoints enter the full
separated-boundary Hilbert space. An empty selection imposes no zero trace. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {l r : ℝ}

noncomputable def IntervalSeparatedBoundary.ofEnergy (B : IntervalSeparatedBoundary l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hzero : ∀ x ∈ B.zero_sites, u x = 0) :
    IntervalSeparatedSpace B :=
  ⟨IntervalSobolevSpace.ofEnergy hu B.interval_pos,
    (B.subspace_mem_iff _).mpr fun x hx =>
      (representative_ofEnergy hu B.interval_pos (B.site_mem hx)).trans (hzero x hx)⟩

theorem IntervalSeparatedBoundary.ofEnergy_state_ae (B : IntervalSeparatedBoundary l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hzero : ∀ x ∈ B.zero_sites, u x = 0) :
    B.stateL (B.ofEnergy hu hzero) =ᵐ[volume.restrict (Ioo l r)] u :=
  (IntervalSobolevSpace.ofEnergy_spec hu B.interval_pos).1

theorem IntervalSeparatedBoundary.ofEnergy_representative (B : IntervalSeparatedBoundary l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hzero : ∀ x ∈ B.zero_sites, u x = 0) :
    EqOn ((B.ofEnergy hu hzero : IntervalSobolevSpace l r).representative B.interval_pos)
      u (Icc l r) := representative_ofEnergy hu B.interval_pos

theorem IntervalSeparatedBoundary.representative_zero (B : IntervalSeparatedBoundary l r)
    (u : IntervalSeparatedSpace B) {x : ℝ} (hx : x ∈ B.zero_sites) :
    u.val.representative B.interval_pos x = 0 :=
  (B.subspace_mem_iff u.val).mp u.property x hx

theorem IntervalSeparatedBoundary.ofEnergy_representative_eq (B : IntervalSeparatedBoundary l r)
    (u : IntervalSeparatedSpace B) :
    B.ofEnergy (u.val.representative_spec B.interval_pos).1
      (fun _ hx => B.representative_zero u hx) = u := by
  apply Subtype.ext
  exact IntervalSobolevSpace.ofEnergy_representative u.val B.interval_pos

end TimeTraps.Analysis
