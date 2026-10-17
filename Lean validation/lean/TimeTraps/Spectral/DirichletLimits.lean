module

public import TimeTraps.Spectral.DirichletRayleigh
public import TimeTraps.Spectral.BudgetAsymptoticLimits
public import TimeTraps.Spectral.RobinDirichletConsistency

@[expose] public section

/-!
The independently attained first eigenvalues of the perfect-absorber cells
are exactly the strong-budget limiting value in the source. This identifies
the limiting number with a physical Dirichlet variational problem; it does
not assert convergence of operators or of arbitrary eigenfunctions.
-/

namespace TimeTraps.Spectral

open Set Filter Topology

noncomputable def perfectAbsorberCell {n : ℕ} {D L : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) : DirichletInterval where
  length := L / (n : ℝ)
  length_pos := div_pos hL (Nat.cast_pos.mpr hn)
  diffusivity := D
  diffusivity_pos := hD
  ends := .both

noncomputable def perfectAbsorberTip {n : ℕ} {D L : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) (left : Bool) : DirichletInterval where
  length := L / (2 * (n : ℝ))
  length_pos := div_pos hL (mul_pos (by norm_num) (Nat.cast_pos.mpr hn))
  diffusivity := D
  diffusivity_pos := hD
  ends := if left then .left else .right

theorem perfectAbsorberCell_principalValue {n : ℕ} {D L : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) :
    (perfectAbsorberCell hn hD hL).principalValue =
      D * Real.pi ^ 2 * (n : ℝ) ^ 2 / L ^ 2 := by
  rw [(perfectAbsorberCell hn hD hL).principalValue_both rfl]
  dsimp [perfectAbsorberCell]
  field_simp [hL.ne', (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

theorem perfectAbsorberTip_principalValue {n : ℕ} {D L : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) (left : Bool) :
    (perfectAbsorberTip hn hD hL left).principalValue =
      D * Real.pi ^ 2 * (n : ℝ) ^ 2 / L ^ 2 := by
  cases left
  · rw [(perfectAbsorberTip hn hD hL false).principalValue_right rfl]
    dsimp [perfectAbsorberTip]
    field_simp [hL.ne', (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']
    ring
  · rw [(perfectAbsorberTip hn hD hL true).principalValue_left rfl]
    dsimp [perfectAbsorberTip]
    field_simp [hL.ne', (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']
    ring

theorem perfectAbsorberCell_minimum {n : ℕ} {D L : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) :
    IsLeast (perfectAbsorberCell hn hD hL).rayleighValues
      (D * Real.pi ^ 2 * (n : ℝ) ^ 2 / L ^ 2) := by
  rw [← perfectAbsorberCell_principalValue hn hD hL,
    (perfectAbsorberCell hn hD hL).principalValue_eq]
  exact (perfectAbsorberCell hn hD hL).rayleigh_minimum

theorem spectralBudgetValue_strong_dirichlet_limit {n : ℕ} {D L : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hL : 0 < L) :
    Tendsto (spectralBudgetValue n D L) atTop
      (𝓝 (perfectAbsorberCell hn hD hL).principalValue) := by
  rw [perfectAbsorberCell_principalValue]
  exact spectralBudgetValue_strong_limit hn hD hL

theorem dirichlet_empty_mixed_principalValue (P : DirichletInterval) (he : P.ends = .right)
    {k : ℝ} (hk : P.length * k =
      dirichletPhaseCapacity (∅ : Finset Unit) (fun _ => 0) 0 0 false true k) :
    P.principalValue = P.diffusivity * k ^ 2 := by
  rw [(dirichlet_empty_mixed_root P.length_pos).mp hk, P.principalValue_eq]
  simp only [DirichletInterval.waveNumber, he]

theorem dirichlet_empty_double_principalValue (P : DirichletInterval) (he : P.ends = .both)
    {k : ℝ} (hk : P.length * k =
      dirichletPhaseCapacity (∅ : Finset Unit) (fun _ => 0) 0 0 true true k) :
    P.principalValue = P.diffusivity * k ^ 2 := by
  rw [(dirichlet_empty_double_root P.length_pos).mp hk, P.principalValue_eq]
  simp only [DirichletInterval.waveNumber, he]

end TimeTraps.Spectral
