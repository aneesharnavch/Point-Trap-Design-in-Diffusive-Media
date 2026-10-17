module

public import TimeTraps.Probability.GraphConservativeSampledLaw
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! The finite chronological law for two distinct observation times.
These deterministic index identities expose the actual earlier and later
states, including a possible observation at time zero. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem observationPair_sort {s t : ℝ≥0} (hst : s < t) :
    ({s, t} : Finset ℝ≥0).sort (· ≤ ·) = [s, t] := by
  rw [Finset.sort_insert (· ≤ ·) (fun b hb => by
    have hb' : b = t := Finset.mem_singleton.mp hb
    exact hb' ▸ hst.le) (by simpa only [Finset.mem_singleton] using hst.ne),
    Finset.sort_singleton]

theorem observationPair_durations {s t : ℝ≥0} (hst : s < t) :
    observationDurations 0 (({s, t} : Finset ℝ≥0).sort (· ≤ ·)) = [s, t - s] := by
  rw [observationPair_sort hst]
  simp only [observationDurations, tsub_zero]

variable {α : Type*}

theorem observationState_time (I : Finset ℝ≥0)
    (q : Fin (observationDurations 0 (I.sort (· ≤ ·))).length → α)
    (t : I) (i : Fin (observationDurations 0 (I.sort (· ≤ ·))).length)
    (hi : elapsedObservationTime 0 (observationDurations 0 (I.sort (· ≤ ·))) i = t.val) :
    observationState I q t = q i := by
  apply congrArg q
  apply (observationTimeIndex I).injective
  rw [(observationTimeIndex I).apply_symm_apply]
  exact Subtype.ext ((observationTimeIndex_time I i).trans hi).symm

theorem finiteMarkovKernel_pair_lintegral [MeasurableSpace α]
    (K : ℝ≥0 → Kernel α α) [∀ t, IsMarkovKernel (K t)] (s u : ℝ≥0) (x : α)
    {F : α × α → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F (q 0, q 1) ∂finiteMarkovKernel K [s, u] x) =
      ∫⁻ y, ∫⁻ z, F (y, z) ∂K u y ∂K s x := by
  have hh : Measurable (fun q : Fin 2 → α => F (q 0, q 1)) :=
    hF.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  have hc := finiteMarkovKernel_lintegral_cons K s [u] x hh
  apply hc.trans
  apply lintegral_congr
  intro y
  have hhead : (finiteMarkovKernel K [u] y).map (fun q => q 0) = K u y := by
    rw [← Kernel.map_apply _ (measurable_pi_apply 0)]
    exact congrArg (fun k => k y) (finiteMarkovKernel_head K u [])
  have hm : Measurable (fun z : α => F (y, z)) := hF.comp (measurable_const.prodMk measurable_id)
  have he := lintegral_map (μ := finiteMarkovKernel K [u] y) hm (measurable_pi_apply (0 : Fin 1))
  exact he.symm.trans (congrArg (fun μ : Measure α => ∫⁻ z, F (y, z) ∂μ) hhead)

end TimeTraps.Probability
