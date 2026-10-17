module

public import TimeTraps.Probability.BrownianAffineLocalTimeRange
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Interval

@[expose] public section

/-! For fixed lattice spacing, take only a countable intersection of
fixed-level support events. On it, every finite horizon has a finite set
of possibly active lattice corrections, uniformly over all earlier times.
Finiteness is derived from the actual compact path range. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

def affineBrownianLatticeRegular (x σ L : ℝ) (ω : ℕ → ℝ) : Prop :=
  ∀ j : ℤ, affineBrownianLocalTimeRegular x σ ((j : ℝ) * L) ω

def affineBrownianLatticeActive (x σ L : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : Set ℤ :=
  {j | ∃ s ∈ Icc (0 : ℝ≥0) T,
    affineBrownianTanakaCorrection x σ ((j : ℝ) * L) s ω ≠ 0 ∨
      affineBrownianOccupationDensity x σ ((j : ℝ) * L) s ω ≠ 0}

theorem affineBrownianLatticeRegular_measurableSet (x σ L : ℝ) :
    MeasurableSet {ω | affineBrownianLatticeRegular x σ L ω} := by
  simp only [affineBrownianLatticeRegular, ofPred_forall]
  exact MeasurableSet.iInter (fun j => affineBrownianLocalTimeRegular_measurableSet x σ ((j : ℝ) * L))

theorem affineBrownianLatticeRegular_ae (x σ L : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, affineBrownianLatticeRegular x σ L ω :=
  ae_all_iff.mpr (fun j => affineBrownianLocalTimeRegular_ae x σ ((j : ℝ) * L))

theorem affineBrownianLattice_range_finite (x σ : ℝ) {L : ℝ} (hL : 0 < L)
    (T : ℝ≥0) {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) :
    {j : ℤ | (j : ℝ) * L ∈ affineBrownianPathRange x σ T ω}.Finite := by
  have hc := affineBrownianPathRange_compact x σ T hω
  obtain ⟨M, hM⟩ := (hc.image continuous_abs).bddAbove
  apply (Set.finite_Icc ⌈-M / L⌉ ⌊M / L⌋).subset
  intro j hj
  have hbound : |(j : ℝ) * L| ≤ M := hM (mem_image_of_mem abs hj)
  have hpair := abs_le.mp hbound
  exact ⟨Int.ceil_le.mpr ((div_le_iff₀ hL).mpr hpair.1),
    Int.le_floor.mpr ((le_div_iff₀ hL).mpr hpair.2)⟩

theorem affineBrownianLatticeActive_finite {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) (T : ℝ≥0) :
    (affineBrownianLatticeActive x σ L T ω).Finite := by
  apply (affineBrownianLattice_range_finite x σ hL T (hω 0).2.1).subset
  intro j hj
  by_contra hn
  obtain ⟨s, hs, hnz⟩ := hj
  have hz := affineBrownianLocalTime_vanishes_outside_range hσ (hω j) T hn s hs
  exact hnz.elim (fun h => h hz.1) (fun h => h hz.2)

theorem affineBrownianLattice_uniform_finite_support {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) (T : ℝ≥0) :
    ∃ J : Finset ℤ, ∀ j ∉ J, ∀ s ∈ Icc (0 : ℝ≥0) T,
      affineBrownianTanakaCorrection x σ ((j : ℝ) * L) s ω = 0 ∧
        affineBrownianOccupationDensity x σ ((j : ℝ) * L) s ω = 0 := by
  classical
  let hfinite := affineBrownianLatticeActive_finite hσ hL hω T
  refine ⟨hfinite.toFinset, ?_⟩
  intro j hj s hs
  have hnot : j ∉ affineBrownianLatticeActive x σ L T ω := by
    simpa only [Set.Finite.mem_toFinset] using hj
  constructor
  · by_contra hn
    exact hnot ⟨s, hs, Or.inl hn⟩
  · by_contra hn
    exact hnot ⟨s, hs, Or.inr hn⟩

theorem affineBrownianLattice_uniform_finite_support_ae (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      ∃ J : Finset ℤ, ∀ j ∉ J, ∀ s ∈ Icc (0 : ℝ≥0) T,
        affineBrownianTanakaCorrection x σ ((j : ℝ) * L) s ω = 0 ∧
          affineBrownianOccupationDensity x σ ((j : ℝ) * L) s ω = 0 :=
  (affineBrownianLatticeRegular_ae x σ L).mono
    (fun _ hω T => affineBrownianLattice_uniform_finite_support hσ hL hω T)

end TimeTraps.Probability
