module

public import TimeTraps.Probability.ReflectedGaussianL2Feller
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

/-! The actual uniform-L2 evolution is a strongly continuous contraction
semigroup, with time parameter equal to Gaussian variance. Composition
and the zero identity transfer from the actual Feller evolution through
its proved dense embedding. Strong continuity follows from uniform
approximation of every L2 orbit by continuous Feller orbits. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal ProbabilityTheory Topology

theorem reflectedGaussianL2Operator_zero (L : ℝ) (hL : 0 < L) :
    reflectedGaussianL2Operator L hL 0 = ContinuousLinearMap.id ℝ (ReflectedUniformL2 L hL) := by
  apply DFunLike.ext'
  apply Continuous.ext_on (reflectedFellerToL2_denseRange L hL)
    (reflectedGaussianL2Operator L hL 0).continuous continuous_id
  rintro _ ⟨f, rfl⟩
  rw [reflectedGaussianL2Operator_feller, reflectedFellerOperator_zero]
  rfl

theorem reflectedGaussianL2Operator_comp (L : ℝ) (hL : 0 < L) (v₁ v₂ : ℝ≥0) :
    (reflectedGaussianL2Operator L hL v₁).comp (reflectedGaussianL2Operator L hL v₂) =
      reflectedGaussianL2Operator L hL (v₁ + v₂) := by
  apply DFunLike.ext'
  apply Continuous.ext_on (reflectedFellerToL2_denseRange L hL)
    ((reflectedGaussianL2Operator L hL v₁).continuous.comp
      (reflectedGaussianL2Operator L hL v₂).continuous)
    (reflectedGaussianL2Operator L hL (v₁ + v₂)).continuous
  rintro _ ⟨f, rfl⟩
  change reflectedGaussianL2Operator L hL v₁
    (reflectedGaussianL2Operator L hL v₂ (reflectedFellerToL2 L hL f)) = _
  rw [reflectedGaussianL2Operator_feller, reflectedGaussianL2Operator_feller,
    reflectedGaussianL2Operator_feller]
  exact congrArg (reflectedFellerToL2 L hL)
    (congrArg (fun A : C(Icc (0 : ℝ) L, ℝ) →L[ℝ] C(Icc (0 : ℝ) L, ℝ) => A f)
      (reflectedFellerOperator_comp L hL v₁ v₂))

theorem reflectedGaussianL2Operator_continuous (L : ℝ) (hL : 0 < L)
    (f : ReflectedUniformL2 L hL) :
    Continuous (fun v : ℝ≥0 => reflectedGaussianL2Operator L hL v f) := by
  obtain ⟨a, ha, hat⟩ := mem_closure_iff_seq_limit.mp ((reflectedFellerToL2_denseRange L hL) f)
  choose g hg using ha
  have hc (n : ℕ) : Continuous (fun v : ℝ≥0 => reflectedGaussianL2Operator L hL v (a n)) := by
    simp_rw [← hg n, reflectedGaussianL2Operator_feller]
    exact (reflectedFellerToL2 L hL).continuous.comp (reflectedFellerOperator_continuous L hL (g n))
  have hu : TendstoUniformly (fun n v => reflectedGaussianL2Operator L hL v (a n))
      (fun v => reflectedGaussianL2Operator L hL v f) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have ht : Tendsto (fun n => dist f (a n)) atTop (𝓝 0) := by
      simpa only [dist_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f)).dist hat
    filter_upwards [ht.eventually (Iio_mem_nhds hε)] with n hn
    intro v
    calc
      dist (reflectedGaussianL2Operator L hL v f) (reflectedGaussianL2Operator L hL v (a n)) =
          ‖reflectedGaussianL2Operator L hL v (f - a n)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ ‖f - a n‖ := reflectedGaussianL2Operator_contraction L hL v _
      _ = dist f (a n) := (dist_eq_norm _ _).symm
      _ < ε := hn
  exact hu.continuous (Eventually.of_forall hc).frequently

theorem reflectedGaussianL2Operator_tendsto_zero (L : ℝ) (hL : 0 < L)
    (f : ReflectedUniformL2 L hL) :
    Tendsto (fun v : ℝ≥0 => reflectedGaussianL2Operator L hL v f) (𝓝 0) (𝓝 f) := by
  simpa only [reflectedGaussianL2Operator_zero, ContinuousLinearMap.id_apply] using
    (reflectedGaussianL2Operator_continuous L hL f).tendsto 0

end TimeTraps.Probability
