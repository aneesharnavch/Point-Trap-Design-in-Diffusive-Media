module

public import TimeTraps.Probability.ReflectedFellerDomainReconstruction

@[expose] public section

/-! Classical spatial derivatives of the actual folded continuous
extension of a C² Neumann test. The endpoint statements use the physical
one-sided interval derivatives and preserve both zero slope traces. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped Topology

theorem ReflectedNeumannC2.extension_within_derivative {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (x : ℝ) (hx : x ∈ Icc 0 L) :
    HasDerivWithinAt (reflectedFellerExtension L hL F.valueMap) (F.slope x) (Icc 0 L) x := by
  have hd : HasDerivAt (fun y => reflectedFellerRawPrimitive L hL F.slopeMap y + F.value 0)
      (F.slope x) x := by
    apply ((reflectedFellerRawPrimitive_derivative L hL F.slopeMap x).add_const (F.value 0)).congr_deriv
    exact reflectedFellerExtension_on_interval L hL F.slopeMap ⟨x, hx⟩
  apply hd.hasDerivWithinAt.congr_of_mem
  · intro y hy
    rw [reflectedFellerExtension_on_interval L hL F.valueMap ⟨y, hy⟩]
    have he := congrArg (fun g : C(Icc (0 : ℝ) L, ℝ) => g ⟨y, hy⟩) (F.primitive_slope hL)
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one] at he
    change reflectedFellerRawPrimitive L hL F.slopeMap y = F.value y - F.value 0 at he
    change F.value y = reflectedFellerRawPrimitive L hL F.slopeMap y + F.value 0
    linarith
  · exact hx

theorem ReflectedNeumannC2.extension_derivative {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (x : ℝ) (hx : x ∈ Ioo 0 L) :
    HasDerivAt (reflectedFellerExtension L hL F.valueMap) (F.slope x) x :=
  (F.extension_within_derivative hL x ⟨hx.1.le, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)

theorem ReflectedNeumannC2.extension_second_derivative {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (x : ℝ) (hx : x ∈ Ioo 0 L) :
    deriv (deriv (reflectedFellerExtension L hL F.valueMap)) x = F.curvature x := by
  have hd : HasDerivAt (deriv (reflectedFellerExtension L hL F.valueMap)) (F.curvature x) x := by
    apply (F.slope_derivative x hx).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (F.extension_derivative hL y hy).deriv
  exact hd.deriv

end TimeTraps.Probability
