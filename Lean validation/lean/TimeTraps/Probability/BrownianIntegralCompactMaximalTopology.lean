module

public import TimeTraps.Probability.BrownianIntegralMaximalPathwise
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

/-! Countable dense evaluations recover the actual norm of a continuous
function on a compact time space. They also establish measurability of
continuous-path-valued random variables from their time evaluations. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology NNReal ENNReal

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

theorem compactPath_norm_eq_dense_sup (f : C(K, ℝ)) (d : ℕ → K) (hd : DenseRange d) :
    ‖f‖ = ⨆ n, ‖f (d n)‖ := by
  have hb : BddAbove (range (fun n => ‖f (d n)‖)) := by
    refine ⟨‖f‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact f.norm_coe_le_norm (d n)
  apply le_antisymm
  · apply f.norm_le_of_nonempty.mpr
    intro x
    have hc : IsClosed {x : K | ‖f x‖ ≤ ⨆ n, ‖f (d n)‖} :=
      isClosed_le f.continuous.norm continuous_const
    exact hd.induction_on x hc (fun n => le_ciSup hb n)
  · exact ciSup_le (fun n => f.norm_coe_le_norm (d n))

theorem compactPath_runningMax_tendsto (f : C(K, ℝ)) (d : ℕ → K) (hd : DenseRange d) :
    Tendsto (fun n => finiteRunningMax (fun k => ‖f (d k)‖) n) atTop (𝓝 ‖f‖) := by
  have hm : Monotone (fun n => finiteRunningMax (fun k => ‖f (d k)‖) n) :=
    monotone_nat_of_le_succ (fun n => le_max_left _ _)
  apply tendsto_atTop_isLUB hm
  constructor
  · rintro _ ⟨n, rfl⟩
    exact (finiteRunningMax_le_iff _ n _).mpr (fun k _ => f.norm_coe_le_norm (d k))
  · intro c hc
    rw [compactPath_norm_eq_dense_sup f d hd]
    apply ciSup_le
    intro n
    exact (le_finiteRunningMax (fun k => ‖f (d k)‖) le_rfl).trans (hc (mem_range_self n))

variable [SecondCountableTopology K]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem compactPath_norm_measurable (F : Ω → C(K, ℝ))
    (hF : ∀ t, Measurable (fun ω => F ω t)) : Measurable (fun ω => ‖F ω‖) := by
  have he : (fun ω => ‖F ω‖) = fun ω => ⨆ n, ‖F ω (denseSeq K n)‖ :=
    funext (fun ω => compactPath_norm_eq_dense_sup (F ω) (denseSeq K) (denseRange_denseSeq K))
  rw [he]
  exact Measurable.iSup (fun n => (hF (denseSeq K n)).norm)

theorem compactPath_stronglyMeasurable [LocallyCompactSpace K] (F : Ω → C(K, ℝ))
    (hF : ∀ t, Measurable (fun ω => F ω t)) : StronglyMeasurable F := by
  let : MeasurableSpace C(K, ℝ) := borel C(K, ℝ)
  have : BorelSpace C(K, ℝ) := ⟨rfl⟩
  have hnorm (g : C(K, ℝ)) : Measurable (fun ω => ‖F ω - g‖) :=
    compactPath_norm_measurable (fun ω => F ω - g) (fun t => (hF t).sub measurable_const)
  have hmeas : Measurable F := by
    apply measurable_of_isOpen
    intro U hU
    let J := {p : C(K, ℝ) × ℝ // Metric.ball p.1 p.2 ⊆ U}
    let V : J → Set C(K, ℝ) := fun p => Metric.ball p.val.1 p.val.2
    have he : (⋃ p, V p) = U := by
      ext x
      constructor
      · intro hx
        obtain ⟨p, hp⟩ := mem_iUnion.mp hx
        exact p.property hp
      · intro hx
        obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
        exact mem_iUnion.mpr ⟨⟨(x, r), hrU⟩, Metric.mem_ball_self hr⟩
    obtain ⟨S, hSc, hS⟩ := isOpen_iUnion_countable V (fun _ => Metric.isOpen_ball)
    rw [← he, ← hS]
    simp only [preimage_iUnion]
    apply MeasurableSet.biUnion hSc
    intro p _
    change MeasurableSet {ω | dist (F ω) p.val.1 < p.val.2}
    simpa only [dist_eq_norm] using measurableSet_lt (hnorm p.val.1) measurable_const
  exact hmeas.stronglyMeasurable

end TimeTraps.Probability
