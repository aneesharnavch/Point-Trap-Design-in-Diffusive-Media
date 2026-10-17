module

public import TimeTraps.Interval.SourceDensityPerturbationModel

@[expose] public section

/-! The source-facing correction vector is the unique solution of the
finite Dirichlet tridiagonal system, including its two zero endpoint
values. N=n+1 throughout. -/

namespace TimeTraps.Interval

open TimeTraps.Analysis

theorem StationaryPerturbation.correction_spec (S : StationaryPerturbation) (n : ℕ) :
    S.correction n 0 = 0 ∧ S.correction n (Fin.last (n + 1)) = 0 ∧
      ∀ i : Fin n, discreteSecondDifference (S.correction n) i =
        -4 * ((n : ℝ) + 1) * gridIFTForcing S.profile i := by
  refine ⟨nodalStrength_first _, nodalStrength_last _, ?_⟩
  exact gridIFTBranch_first_variation S.profile S.profile_contDiff S.scale S.scale_pos

theorem StationaryPerturbation.correction_unique (S : StationaryPerturbation) {n : ℕ}
    (r : Fin (n + 2) → ℝ) (hleft : r 0 = 0) (hright : r (Fin.last (n + 1)) = 0)
    (hr : ∀ i : Fin n, discreteSecondDifference r i =
      -4 * ((n : ℝ) + 1) * gridIFTForcing S.profile i) : r = S.correction n := by
  let v : Fin n → ℝ := fun i => r i.castSucc.succ
  have hv : nodalStrength v = r := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [nodalStrength_first] using hleft.symm
    · refine Fin.lastCases ?_ (fun i => ?_) k
      · change nodalStrength v (Fin.last (n + 1)) = r (Fin.last (n + 1))
        simpa only [nodalStrength_last] using hright.symm
      · exact nodalStrength_trap v i
  have hveq : ∀ i : Fin n, discreteSecondDifference (nodalStrength v) i =
      -4 * ((n : ℝ) + 1) * gridIFTForcing S.profile i := by rwa [hv]
  have hsol := gridIFTBranch_correction_unique S.profile S.profile_contDiff S.scale S.scale_pos v hveq
  rw [← hv, hsol]
  rfl

end TimeTraps.Interval
