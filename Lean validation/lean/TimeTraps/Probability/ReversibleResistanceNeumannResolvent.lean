module

public import TimeTraps.Probability.ReflectedPositivePotentialResolvent
public import TimeTraps.Probability.ReversibleResistanceNeumannDomain

@[expose] public section

/-! Every continuous physical forcing is the positive resolvent image
of a genuine divergence-form Neumann test for the original medium. The
construction only differentiates the state and flux, retaining continuous
positive conductance and speed density without extra smoothness. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Interval
open scoped NNReal Topology

def ReflectedNeumannC2.physicalTest (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) : ReversibleNeumannTest A where
  value := reversibleResistanceNeumannTest A F
  flux := reversibleResistanceNeumannFlux A F
  generator := reversibleResistanceNeumannGenerator A F
  value_continuous := reversibleResistanceNeumannTest_continuous A F
  flux_continuous := reversibleResistanceNeumannFlux_continuous A F
  generator_continuous := reversibleResistanceNeumannGenerator_continuous A F
  value_derivative := fun _ hx => reversibleResistanceNeumannTest_hasDerivAt A F hx
  flux_derivative := by
    intro x hx
    have hd : HasDerivAt (reversibleResistanceNeumannFlux A F)
        (F.curvature (A.resistance x) / A.conductance x) x := by
      convert! (F.slope_derivative _ (reversibleResistance_interior A hx)).comp x
        (A.resistance_hasDerivAt hx) using 1
      simp only [mul_one_div]
    convert! hd using 1
    unfold reversibleResistanceNeumannGenerator
    field_simp [(A.conductance_pos x (Ioo_subset_Icc_self hx)).ne',
      (A.source.positive x (Ioo_subset_Icc_self hx)).ne']
  neumann_left := (reversibleResistanceNeumannFlux_endpoints A F).1
  neumann_right := (reversibleResistanceNeumannFlux_endpoints A F).2

theorem reversibleNeumann_resolvent_test_exists (A : IntervalMedium)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right))
    {α : ℝ} (hα : 0 < α) :
    ∃ H : ReversibleNeumannTest A, ∀ x ∈ Icc A.source.left A.source.right,
      α * H.value x - H.generator x = g x := by
  let c : C(Icc (0 : ℝ) A.resistanceLength, ℝ) :=
    ⟨fun y => A.resistanceSpeed y.val, A.resistanceSpeed_continuous.comp continuous_subtype_val⟩
  let f : C(Icc (0 : ℝ) A.resistanceLength, ℝ) :=
    ⟨fun y => g (A.resistanceInverse y.val),
      (hg.comp_continuous A.resistanceInverse_continuous A.resistanceInverse_mem).comp
        continuous_subtype_val⟩
  obtain ⟨F, hF⟩ := reflectedPositiveSpeed_resolvent_test_exists A.resistanceLength
    A.resistanceLength_pos c f (fun y => A.resistanceSpeed_pos y.val) hα
  refine ⟨F.physicalTest A, fun x hx => ?_⟩
  have he := hF ⟨A.resistance x, A.resistance_mem hx⟩
  change α * F.value (A.resistance x) -
    F.curvature (A.resistance x) / A.resistanceSpeed (A.resistance x) =
      g (A.resistanceInverse (A.resistance x)) at he
  rw [A.resistanceSpeed_resistance hx, A.resistanceInverse_resistance hx] at he
  exact he

end TimeTraps.Probability

end
