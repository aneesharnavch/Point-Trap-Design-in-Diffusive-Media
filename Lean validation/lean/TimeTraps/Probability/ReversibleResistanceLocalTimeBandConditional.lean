module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandReconstruction
public import TimeTraps.Probability.ReversibleResistanceSurvivalConditional

@[expose] public section

/-! Conditional survival given the actual physical particle path. The
independent exponential coordinate is excluded from the conditioning
sigma-algebra. Reconstruction supplies an almost-everywhere measurable
survival weight in this raw sigma-algebra, and the tower property transfers
the already proved driving-path conditional identity. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

@[instance_reducible] noncomputable def reversibleResistanceKilledParticleSigma
    (A : IntervalMedium) (x : ℝ) : MeasurableSpace ((ℕ → ℝ) × ℝ) :=
  (reversibleResistanceParticleSigma A x).comap (Prod.fst : (ℕ → ℝ) × ℝ → (ℕ → ℝ))

theorem reversibleResistanceKilledParticleSigma_eq (A : IntervalMedium) (x : ℝ) :
    reversibleResistanceKilledParticleSigma A x =
      (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)).comap
        (fun p : (ℕ → ℝ) × ℝ => fun t => reversibleResistancePath A x t p.1) := by
  rw [reversibleResistanceKilledParticleSigma, reversibleResistanceParticleSigma,
    MeasurableSpace.comap_comp]
  rfl

theorem reversibleResistanceKilledParticleSigma_le_driving (A : IntervalMedium) (x : ℝ) :
    reversibleResistanceKilledParticleSigma A x ≤
      (inferInstance : MeasurableSpace (ℕ → ℝ)).comap (Prod.fst : (ℕ → ℝ) × ℝ → (ℕ → ℝ)) :=
  MeasurableSpace.comap_mono (reversibleResistanceParticleSigma_le A x)

theorem reversibleResistanceAtomicSurvival_killed_particle_aestronglyMeasurable
    {ι : Type*} [Fintype ι] (A : IntervalMedium) (x : ℝ) (a κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo A.source.left A.source.right) (T : ℝ≥0) :
    AEStronglyMeasurable[reversibleResistanceKilledParticleSigma A x]
      (fun p : (ℕ → ℝ) × ℝ => reversibleResistanceAtomicSurvival A x a κ T p.1)
      (exponentialKillingMeasure brownianDyadicMeasure) := by
  obtain ⟨g, hgm, hge⟩ := reversibleResistanceAtomicSurvival_particle_aestronglyMeasurable A x a κ ha T
  refine ⟨g ∘ Prod.fst, hgm.comp_measurable (comap_measurable Prod.fst), ?_⟩
  exact (Measure.quasiMeasurePreserving_fst (μ := brownianDyadicMeasure) (ν := expMeasure 1)).ae_eq hge

theorem reversibleResistanceAttainmentLifetime_particle_condExp
    {ι : Type*} [Fintype ι] (A : IntervalMedium) (x : ℝ) (a κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo A.source.left A.source.right)
    (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (ht : 0 ≤ t) :
    (exponentialKillingMeasure brownianDyadicMeasure)[
      {p | (t : WithTop ℝ) < reversibleResistanceAttainmentLifetime A x a κ p}.indicator
        (fun _ => (1 : ℝ)) | reversibleResistanceKilledParticleSigma A x]
      =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
        (fun p => reversibleResistanceAtomicSurvival A x a κ t.toNNReal p.1) := by
  let _ := exponentialKilling_probability brownianDyadicMeasure
  have hbase := reversibleResistanceAttainmentLifetime_condExp A x a κ hκ t ht
  have hm₂ : (inferInstance : MeasurableSpace (ℕ → ℝ)).comap
      (Prod.fst : (ℕ → ℝ) × ℝ → (ℕ → ℝ)) ≤
      (inferInstance : MeasurableSpace ((ℕ → ℝ) × ℝ)) := measurable_fst.comap_le
  have hm₁₂ := reversibleResistanceKilledParticleSigma_le_driving A x
  have hg : Integrable (fun p : (ℕ → ℝ) × ℝ =>
      reversibleResistanceAtomicSurvival A x a κ t.toNNReal p.1)
      (exponentialKillingMeasure brownianDyadicMeasure) := integrable_condExp.congr hbase
  exact (condExp_condExp_of_le hm₁₂ hm₂).symm.trans
    ((condExp_congr_ae hbase).trans
      (condExp_of_aestronglyMeasurable' (hm₁₂.trans hm₂)
        (reversibleResistanceAtomicSurvival_killed_particle_aestronglyMeasurable A x a κ ha t.toNNReal) hg))

end TimeTraps.Probability
