module

public import TimeTraps.Probability.ReflectedFellerLaplaceElliptic
public import Mathlib.Topology.MetricSpace.Contracting

@[expose] public section

/-! A strictly positive continuous potential is handled by a contraction
of the actual reflected Neumann Laplace resolvent. The contraction
constant follows from the actual minimum and maximum of the potential;
no resolvent solvability or process uniqueness is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal Topology

theorem reflectedFellerLaplace_sub (L : ℝ) (hL : 0 < L) (D : ℝ)
    {β : ℝ} (hβ : 0 < β) (f g : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerLaplace L hL D β (f - g) =
      reflectedFellerLaplace L hL D β f - reflectedFellerLaplace L hL D β g := by
  unfold reflectedFellerLaplace
  rw [← integral_sub (reflectedFellerLaplace_integrable L hL D hβ f)
    (reflectedFellerLaplace_integrable L hL D hβ g)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  change Real.exp (-β * t) • reflectedFellerTimeOperator L hL D t (f - g) = _
  rw [map_sub, smul_sub]

def reflectedPositivePotentialStep (L : ℝ) (hL : 0 < L) (β : ℝ)
    (q g : C(Icc (0 : ℝ) L, ℝ)) (u : C(Icc (0 : ℝ) L, ℝ)) : C(Icc (0 : ℝ) L, ℝ) :=
  reflectedFellerLaplace L hL 1 β (g + (ContinuousMap.const _ β - q) * u)

theorem reflectedPositivePotentialStep_difference (L : ℝ) (hL : 0 < L)
    {β : ℝ} (hβ : 0 < β) (q g u v : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedPositivePotentialStep L hL β q g u - reflectedPositivePotentialStep L hL β q g v =
      reflectedFellerLaplace L hL 1 β ((ContinuousMap.const _ β - q) * (u - v)) := by
  unfold reflectedPositivePotentialStep
  rw [← reflectedFellerLaplace_sub L hL 1 hβ]
  congr 1
  ring

theorem reflectedPositivePotential_complement_norm (L : ℝ) (q : C(Icc (0 : ℝ) L, ℝ))
    {m β : ℝ} (hmb : m ≤ β) (hm : ∀ y, m ≤ q y) (hβ : ∀ y, q y ≤ β) :
    ‖ContinuousMap.const _ β - q‖ ≤ β - m := by
  apply (ContinuousMap.norm_le _ (sub_nonneg.mpr hmb)).mpr
  intro y
  change |β - q y| ≤ β - m
  rw [abs_of_nonneg (sub_nonneg.mpr (hβ y))]
  exact sub_le_sub_left (hm y) β

theorem reflectedPositivePotentialStep_dist_le (L : ℝ) (hL : 0 < L)
    {m β : ℝ} (hβ : 0 < β) (hmb : m ≤ β)
    (q g : C(Icc (0 : ℝ) L, ℝ)) (hmq : ∀ y, m ≤ q y) (hqβ : ∀ y, q y ≤ β)
    (u v : C(Icc (0 : ℝ) L, ℝ)) :
    dist (reflectedPositivePotentialStep L hL β q g u) (reflectedPositivePotentialStep L hL β q g v) ≤
      ((β - m) / β) * dist u v := by
  rw [dist_eq_norm, dist_eq_norm, reflectedPositivePotentialStep_difference L hL hβ]
  calc
    _ ≤ ‖(ContinuousMap.const _ β - q) * (u - v)‖ / β := reflectedFellerLaplace_norm_le L hL 1 hβ _
    _ ≤ ((β - m) * ‖u - v‖) / β := div_le_div_of_nonneg_right
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (reflectedPositivePotential_complement_norm L q hmb hmq hqβ) (norm_nonneg _))) hβ.le
    _ = _ := by ring

theorem reflectedPositivePotentialStep_contracting (L : ℝ) (hL : 0 < L)
    {m β : ℝ} (hm : 0 < m) (hmb : m ≤ β)
    (q g : C(Icc (0 : ℝ) L, ℝ)) (hmq : ∀ y, m ≤ q y) (hqβ : ∀ y, q y ≤ β) :
    ContractingWith ⟨(β - m) / β, div_nonneg (sub_nonneg.mpr hmb) (hm.le.trans hmb)⟩
      (reflectedPositivePotentialStep L hL β q g) := by
  have hβ : 0 < β := hm.trans_le hmb
  refine ⟨?_, LipschitzWith.of_dist_le_mul (fun u v =>
    reflectedPositivePotentialStep_dist_le L hL hβ hmb q g hmq hqβ u v)⟩
  change (β - m) / β < 1
  exact (div_lt_one hβ).mpr (sub_lt_self β hm)

end TimeTraps.Probability

end
