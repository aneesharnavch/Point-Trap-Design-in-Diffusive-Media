module

public import TimeTraps.Interval.ReflectedMeanKinkData
public import TimeTraps.Analysis.ReflectedMeanKinkGreen

@[expose] public section

/-! Every original homogeneous physical design has an exact global
quadratic-plus-kinks representative on [0,L]. The proof tests its full
H¹ weak equation, rather than assuming piecewise regularity or a
Feynman–Kac formula. Ordered interior sites and positive strengths are
those of the existing IntervalDesign, and reflecting slopes follow from
its proved source conservation. -/

noncomputable section

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

def IntervalDesign.meanKinkPotential (E : IntervalDesign (homogeneous L D hL hD) n K) : ℝ → ℝ :=
  finiteKinkPotential E.meanKinkBase Finset.univ E.geometry.site E.meanKinkCoefficient

theorem IntervalDesign.meanKinkPotential_eq
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    EqOn E.meanKinkPotential E.state (Icc (0 : ℝ) L) := by
  intro y hy
  have hu : IntervalEnergy E.state 0 L := by
    have he := E.equation.energy
    rw [E.homogeneous_source] at he
    exact he
  have hv : IntervalEnergy (fun z => |z - y|) E.geometry.source.left E.geometry.source.right := by
    rw [E.homogeneous_source]
    exact intervalEnergy_abs_sub y 0 L hL.le
  have hw := E.equation.weak_form (fun z => |z - y|) hv
  rw [E.homogeneous_source, E.homogeneous_conductance] at hw
  change (∫ z in (0 : ℝ)..L, D * deriv E.state z * deriv (fun z => |z - y|) z) +
    (∑ i, E.strength i * E.state (E.geometry.site i) * |E.geometry.site i - y|) =
      ∫ z in (0 : ℝ)..L, 1 * |z - y| at hw
  simp only [one_mul] at hw
  have hp : (∫ z in (0 : ℝ)..L, D * deriv E.state z * deriv (fun z => |z - y|) z) =
      D * (E.state L + E.state 0 - 2 * E.state y) := by
    calc
      _ = D * ∫ z in (0 : ℝ)..L, deriv E.state z * deriv (fun z => |z - y|) z := by
        simp only [mul_assoc, intervalIntegral.integral_const_mul]
      _ = _ := by rw [hu.abs_sub_pairing hy]
  rw [hp, interval_integral_abs_sub hy] at hw
  have hs : (∑ i, E.meanKinkCoefficient i * |y - E.geometry.site i|) =
      (∑ i, E.strength i * E.state (E.geometry.site i) * |E.geometry.site i - y|) / (2 * D) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_sub_comm y (E.geometry.site i)]
    unfold IntervalDesign.meanKinkCoefficient
    ring
  change (D * (E.state L + E.state 0) - L ^ 2 / 2 - y ^ 2 + L * y) / (2 * D) +
    (∑ i, E.meanKinkCoefficient i * |y - E.geometry.site i|) = E.state y
  rw [hs, ← add_div]
  apply (div_eq_iff (show 2 * D ≠ 0 by positivity)).mpr
  nlinarith [hw]

theorem IntervalDesign.meanKinkSlope_endpoints
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    finiteKinkSlope E.meanKinkBase Finset.univ E.geometry.site E.meanKinkCoefficient 0 = 0 ∧
      finiteKinkSlope E.meanKinkBase Finset.univ E.geometry.site E.meanKinkCoefficient L = 0 := by
  have ha (i : Fin n) : E.geometry.site i ∈ Ioo 0 L := by
    have hi := E.geometry.site_interior i
    rw [E.homogeneous_source] at hi
    exact hi
  have hs0 (i : Fin n) : Real.sign (0 - E.geometry.site i) = -1 :=
    Real.sign_of_neg (sub_neg.mpr (ha i).1)
  have hsL (i : Fin n) : Real.sign (L - E.geometry.site i) = 1 :=
    Real.sign_of_pos (sub_pos.mpr (ha i).2)
  constructor
  · simp only [finiteKinkSlope, (E.meanKinkBase_hasDerivAt 0).deriv, hs0,
      mul_neg_one, Finset.sum_neg_distrib, E.meanKinkCoefficient_sum]
    ring
  · simp only [finiteKinkSlope, (E.meanKinkBase_hasDerivAt L).deriv, hsL,
      mul_one, E.meanKinkCoefficient_sum]
    ring

theorem IntervalDesign.meanKinkPotential_neumann
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    HasDerivAt E.meanKinkPotential 0 0 ∧ HasDerivAt E.meanKinkPotential 0 L := by
  have ha (i : Fin n) : E.geometry.site i ∈ Ioo 0 L := by
    have hi := E.geometry.site_interior i
    rw [E.homogeneous_source] at hi
    exact hi
  have hdiff := E.meanKinkBase_contDiff.differentiable (by norm_num)
  constructor
  · have he := finiteKinkPotential_hasDerivAt (hdiff.differentiableAt (x := 0))
      Finset.univ E.geometry.site E.meanKinkCoefficient (fun i _ => ne_of_lt (ha i).1)
    rw [E.meanKinkSlope_endpoints.1] at he
    exact he
  · have he := finiteKinkPotential_hasDerivAt (hdiff.differentiableAt (x := L))
      Finset.univ E.geometry.site E.meanKinkCoefficient (fun i _ => ne_of_gt (ha i).2)
    rw [E.meanKinkSlope_endpoints.2] at he
    exact he

theorem IntervalDesign.meanKinkPotential_reaction
    (E : IntervalDesign (homogeneous L D hL hD) n K) (i : Fin n) :
    2 * D * E.meanKinkCoefficient i = E.strength i * E.meanKinkPotential (E.geometry.site i) := by
  have ha : E.geometry.site i ∈ Icc (0 : ℝ) L := by
    have hi := E.geometry.site_interior i
    rw [E.homogeneous_source] at hi
    exact Ioo_subset_Icc_self hi
  rw [E.meanKinkPotential_eq ha]
  exact E.meanKinkCoefficient_reaction i

end TimeTraps.Interval

end
