module

public import TimeTraps.Probability.BrownianLocalTimeTimeReconstruction
public import TimeTraps.Probability.BrownianLocalTimeStieltjesSupport

@[expose] public section

/-! The reconstructed jointly measurable field is a version of the
actual Tanaka compensation with continuous nondecreasing time paths at
each fixed level, on one event valid for all times. The Stieltjes support
is inherited from the actual global path. No spatial continuity or common
event for every level is asserted. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem brownianLocalTimeTimeField_timeSlice_measurable (t : ℝ≥0) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => brownianLocalTimeTimeField p.1 t p.2) := by
  let φ : ℝ × (ℕ → ℝ) → (ℝ × ℝ≥0) × (ℕ → ℝ) := fun p => ((p.1, t), p.2)
  have hφ : Measurable φ := (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hm := brownianLocalTimeTimeField_jointlyMeasurable.comp hφ
  change Measurable (fun p : ℝ × (ℕ → ℝ) => brownianLocalTimeTimeField p.1 t p.2) at hm
  exact hm

theorem brownianLocalTimeTimeField_compensation_ae (a : ℝ) (t : ℝ≥0) :
    brownianLocalTimeTimeField a t =ᵐ[brownianDyadicMeasure]
      brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable a t := by
  have he : brownianLocalTimeTimeField a t =ᵐ[brownianDyadicMeasure]
      brownianLocalTimeGlobalPath a t :=
    (brownianLocalTimeTimeField_globalPath_ae a).mono (fun _ hω => hω t)
  exact he.trans (brownianLocalTimeGlobalPath_compensation_ae a t)

theorem brownianLocalTimeTimeField_memLp (a : ℝ) (t : ℝ≥0) :
    MemLp (brownianLocalTimeTimeField a t) 2 brownianDyadicMeasure :=
  (Lp.memLp (brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable a t)).ae_eq
    (brownianLocalTimeTimeField_compensation_ae a t).symm

theorem brownianLocalTimeTimeField_regular_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Continuous (fun t => brownianLocalTimeTimeField a t ω) ∧
      Monotone (fun t => brownianLocalTimeTimeField a t ω) ∧
      brownianLocalTimeTimeField a 0 ω = 0 ∧
      ∀ t : ℝ≥0, 0 ≤ brownianLocalTimeTimeField a t ω := by
  filter_upwards [brownianLocalTimeTimeField_globalPath_ae a] with ω he
  have hf : (fun t => brownianLocalTimeTimeField a t ω) =
      (fun t => brownianLocalTimeGlobalPath a t ω) := funext he
  refine ⟨?_, ?_, ?_, fun t => brownianLocalTimeTimeField_nonneg a t ω⟩
  · rw [hf]
    exact brownianLocalTimeGlobalPath_continuous a ω
  · rw [hf]
    exact brownianLocalTimeGlobalPath_monotone a ω
  · rw [he 0, brownianLocalTimeGlobalPath_zero]

theorem brownianLocalTimeTimeField_locally_constant_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, brownianDyadicPath t ω ≠ a →
      ∀ᶠ s in 𝓝 t, brownianLocalTimeTimeField a s ω = brownianLocalTimeTimeField a t ω := by
  filter_upwards [brownianLocalTimeTimeField_globalPath_ae a,
    brownianLocalTimeGlobalPath_locally_constant_ae a] with ω he hlocal
  intro t ht
  filter_upwards [hlocal t ht] with s hs
  rw [he s, he t]
  exact hs

theorem brownianLocalTimeTimeField_stieltjes_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∃ f : StieltjesFunction ℝ,
      (∀ t : ℝ, f t = brownianLocalTimeTimeField a t.toNNReal ω) ∧
      f.measure.support ⊆ {t : ℝ | 0 ≤ t ∧ brownianDyadicPath t.toNNReal ω = a} ∧
      ∀ t : ℝ, f.measure {t} = 0 := by
  filter_upwards [brownianLocalTimeTimeField_globalPath_ae a,
    brownianLocalTimeSupportRegular_ae a] with ω he hsupport
  refine ⟨brownianLocalTimeStieltjes a ω, ?_, brownianLocalTimeMeasure_support hsupport, ?_⟩
  · intro t
    exact (he t.toNNReal).symm
  · intro t
    exact brownianLocalTimeMeasure_singleton a ω t

theorem brownianLocalTimeTimeField_measure_Ioc_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ S T : ℝ≥0,
      brownianLocalTimeMeasure a ω (Ioc (S : ℝ) (T : ℝ)) =
        ENNReal.ofReal (brownianLocalTimeTimeField a T ω - brownianLocalTimeTimeField a S ω) := by
  filter_upwards [brownianLocalTimeTimeField_globalPath_ae a] with ω he
  intro S T
  rw [he S, he T]
  exact brownianLocalTimeMeasure_Ioc a ω S T

end TimeTraps.Probability
