module

public import TimeTraps.Probability.ReflectedPositivePotentialResolventData

@[expose] public section

/-! Every strictly positive continuous potential admits a classical
Neumann resolvent test for every continuous load. This is constructed
from the actual constant-coefficient Laplace resolvent, using the proved
contraction, and then upgraded by its genuine C2 regularity theorem. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal Topology

theorem reflectedPositivePotential_neumannC2_exists (L : ℝ) (hL : 0 < L)
    (q g : C(Icc (0 : ℝ) L, ℝ)) (hq : ∀ y, 0 < q y) :
    ∃ F : ReflectedNeumannC2 L, q * F.valueMap - F.curvatureMap = g := by
  have hn : (univ : Set (Icc (0 : ℝ) L)).Nonempty := ⟨⟨0, le_rfl, hL.le⟩, mem_univ _⟩
  obtain ⟨a, _, hmin⟩ := isCompact_univ.exists_isMinOn hn q.continuous.continuousOn
  obtain ⟨b, _, hmax⟩ := isCompact_univ.exists_isMaxOn hn q.continuous.continuousOn
  have hm : 0 < q a := hq a
  have hmb : q a ≤ q b := hmin (mem_univ b)
  have hmq : ∀ y, q a ≤ q y := fun y => hmin (mem_univ y)
  have hqβ : ∀ y, q y ≤ q b := fun y => hmax (mem_univ y)
  have hc := reflectedPositivePotentialStep_contracting L hL hm hmb q g hmq hqβ
  let u : C(Icc (0 : ℝ) L, ℝ) := hc.fixedPoint (reflectedPositivePotentialStep L hL (q b) q g)
  have hu : reflectedPositivePotentialStep L hL (q b) q g u = u := hc.fixedPoint_isFixedPt
  obtain ⟨F, hF, he⟩ := reflectedFellerLaplace_neumannC2 L hL 1 zero_lt_one (hq b)
    (g + (ContinuousMap.const _ (q b) - q) * u)
  have hFu : F.valueMap = u := hF.trans hu
  refine ⟨F, ?_⟩
  ext y
  have hv : F.value y.val = u y := congrArg (fun v : C(Icc (0 : ℝ) L, ℝ) => v y) hFu
  have h := congrArg (fun v : C(Icc (0 : ℝ) L, ℝ) => v y) he
  change q b * F.value y.val - 1 * F.curvature y.val = g y + (q b - q y) * u y at h
  change q y * F.value y.val - F.curvature y.val = g y
  rw [← hv] at h
  nlinarith

theorem reflectedPositiveSpeed_resolvent_test_exists (L : ℝ) (hL : 0 < L)
    (c g : C(Icc (0 : ℝ) L, ℝ)) (hc : ∀ y, 0 < c y) {α : ℝ} (hα : 0 < α) :
    ∃ F : ReflectedNeumannC2 L, ∀ y : Icc (0 : ℝ) L,
      α * F.value y.val - F.curvature y.val / c y = g y := by
  obtain ⟨F, he⟩ := reflectedPositivePotential_neumannC2_exists L hL (α • c) (c * g)
    (fun y => mul_pos hα (hc y))
  refine ⟨F, fun y => ?_⟩
  have h := congrArg (fun v : C(Icc (0 : ℝ) L, ℝ) => v y) he
  change (α * c y) * F.value y.val - F.curvature y.val = c y * g y at h
  apply (mul_right_cancel₀ (hc y).ne')
  rw [sub_mul, div_mul_cancel₀ _ (hc y).ne']
  nlinarith

end TimeTraps.Probability

end
