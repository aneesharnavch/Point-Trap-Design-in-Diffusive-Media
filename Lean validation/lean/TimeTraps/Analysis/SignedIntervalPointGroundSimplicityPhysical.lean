module

public import TimeTraps.Analysis.SignedIntervalPointGroundSimplicityHilbert

@[expose] public section

/-! Every actual physical principal weak eigenstate is a scalar multiple
of any principal state with nonzero left trace, in particular of the
proved positive ground state. All H1 tests and all signed contacts remain. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.principal_weak_hilbert
    (P : SignedIntervalPointProblem ι l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (he : ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        P.principalValue * ∫ x in l..r, u x * v x) :
    ∀ v : IntervalSobolevSpace l r,
      P.form (ofEnergy hu P.interval_pos) v =
        P.principalValue * inner ℝ (ofEnergy hu P.interval_pos).state v.state := by
  apply (P.hilbert_eigen_iff_physical (ofEnergy hu P.interval_pos) P.principalValue).mpr
  intro v hv
  rw [intervalPointForm_congr P.diffusivity P.strength P.site P.interval_pos.le P.site_mem
    (representative_ofEnergy hu P.interval_pos) (fun _ _ => rfl), he v hv]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le P.interval_pos.le
  intro x hx
  change u x * v x = (ofEnergy hu P.interval_pos).representative P.interval_pos x * v x
  rw [representative_ofEnergy hu P.interval_pos (Ioo_subset_Icc_self hx)]

theorem SignedIntervalPointProblem.principal_weak_scalar
    (P : SignedIntervalPointProblem ι l r) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r) (hu₀ : u l ≠ 0)
    (heu : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      intervalPointForm P.diffusivity P.strength P.site l r u w =
        P.principalValue * ∫ x in l..r, u x * w x)
    (hev : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      intervalPointForm P.diffusivity P.strength P.site l r v w =
        P.principalValue * ∫ x in l..r, v x * w x) :
    EqOn v (fun x => (v l / u l) * u x) (Icc l r) := by
  have hUL := representative_ofEnergy hu P.interval_pos (show l ∈ Icc l r from ⟨le_rfl, P.interval_pos.le⟩)
  have hVL := representative_ofEnergy hv P.interval_pos (show l ∈ Icc l r from ⟨le_rfl, P.interval_pos.le⟩)
  have hU₀ : (ofEnergy hu P.interval_pos).representative P.interval_pos l ≠ 0 := by
    rwa [hUL]
  have he := P.principal_hilbert_scalar (ofEnergy hu P.interval_pos) (ofEnergy hv P.interval_pos)
    hU₀ (P.principal_weak_hilbert hu heu) (P.principal_weak_hilbert hv hev)
  rw [hUL, hVL] at he
  intro x hx
  have hx' := congrArg (evalL P.interval_pos x hx) he
  simpa only [map_smul, smul_eq_mul, evalL_ofEnergy] using hx'

end TimeTraps.Analysis
