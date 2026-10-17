module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandLimit
public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandParticle
public import TimeTraps.Probability.ReflectedLocalTimeBandSubsequence
public import TimeTraps.Probability.ReversibleResistanceTimeChangeAtomicHazard

@[expose] public section

/-! Fixed-site local time, finite atomic hazards, and survival weights have
representatives measurable from the actual physical particle path. The
statement is almost-everywhere measurability in the raw path sigma-algebra;
no equality between driving and particle sigma-algebras is claimed. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

theorem reversibleResistanceLocalTime_band_sequence (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) (T : ℝ≥0) :
    ∃ u : ℕ → ℝ, (∀ n, 0 < u n ∧
      u n < min (A.resistance a / 2) ((A.resistanceLength - A.resistance a) / 2)) ∧
      Tendsto u atTop (𝓝 0) ∧ ∀ᵐ ω ∂brownianDyadicMeasure,
        Tendsto (fun n => reversibleResistanceOccupationBand A x a (u n) T ω) atTop
          (𝓝 (reversibleResistanceLocalTime A x a T ω)) :=
  occupationBand_exists_sequence_tendsto_ae
    (reflectedBandWindow_radius_pos ⟨A.resistance a, reversibleResistance_site_interior A ha⟩)
    (fun _ hh hs => reversibleResistanceOccupationBand_error_memLp A x ha T hh hs)
    (reversibleResistanceOccupationBand_square_tendsto A x ha T)

theorem reversibleResistanceLocalTime_particle_aestronglyMeasurable (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) (T : ℝ≥0) :
    AEStronglyMeasurable[reversibleResistanceParticleSigma A x]
      (reversibleResistanceLocalTime A x a T) brownianDyadicMeasure := by
  obtain ⟨u, _, _, hAE⟩ := reversibleResistanceLocalTime_band_sequence A x ha T
  refine ⟨fun ω => limsup (fun n => reversibleResistanceOccupationBand A x a (u n) T ω) atTop,
    (Measurable.limsup (fun n => reversibleResistanceOccupationBand_particle_measurable A x a (u n) T)).stronglyMeasurable, ?_⟩
  filter_upwards [hAE] with ω hω
  exact hω.limsup_eq.symm

theorem reversibleResistanceAtomicHazard_particle_aestronglyMeasurable
    {ι : Type*} [Fintype ι] (A : IntervalMedium) (x : ℝ) (a κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo A.source.left A.source.right) (T : ℝ≥0) :
    AEStronglyMeasurable[reversibleResistanceParticleSigma A x]
      (reversibleResistanceAtomicHazard A x a κ T) brownianDyadicMeasure := by
  classical
  have hs (s : Finset ι) : AEStronglyMeasurable[reversibleResistanceParticleSigma A x]
      (fun ω => ∑ i ∈ s, κ i * reversibleResistanceLocalTime A x (a i) T ω) brownianDyadicMeasure := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (aestronglyMeasurable_const (b := (0 : ℝ)))
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact ((reversibleResistanceLocalTime_particle_aestronglyMeasurable A x (ha i) T).const_mul (κ i)).add ih
  exact hs Finset.univ

theorem reversibleResistanceAtomicSurvival_particle_aestronglyMeasurable
    {ι : Type*} [Fintype ι] (A : IntervalMedium) (x : ℝ) (a κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo A.source.left A.source.right) (T : ℝ≥0) :
    AEStronglyMeasurable[reversibleResistanceParticleSigma A x]
      (reversibleResistanceAtomicSurvival A x a κ T) brownianDyadicMeasure :=
  Real.continuous_exp.comp_aestronglyMeasurable
    (reversibleResistanceAtomicHazard_particle_aestronglyMeasurable A x a κ ha T).neg

end TimeTraps.Probability
