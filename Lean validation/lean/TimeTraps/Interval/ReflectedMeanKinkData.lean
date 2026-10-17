module

public import TimeTraps.Interval.HomogeneousMeanEnergy
public import TimeTraps.Analysis.FiniteKinkCalculus

@[expose] public section

/-! The quadratic base and signed-kink coefficients associated with the
actual homogeneous weak mean state. The source is one, the diffusivity
is D, and the coefficient of each absolute value is κᵢu(aᵢ)/(2D). -/

noncomputable section

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

def IntervalDesign.meanKinkBase (E : IntervalDesign (homogeneous L D hL hD) n K)
    (z : ℝ) : ℝ :=
  (D * (E.state L + E.state 0) - L ^ 2 / 2 - z ^ 2 + L * z) / (2 * D)

def IntervalDesign.meanKinkCoefficient (E : IntervalDesign (homogeneous L D hL hD) n K)
    (i : Fin n) : ℝ := E.strength i * E.state (E.geometry.site i) / (2 * D)

theorem IntervalDesign.meanKinkBase_contDiff
    (E : IntervalDesign (homogeneous L D hL hD) n K) : ContDiff ℝ 2 E.meanKinkBase := by
  unfold IntervalDesign.meanKinkBase
  fun_prop

theorem IntervalDesign.meanKinkBase_hasDerivAt
    (E : IntervalDesign (homogeneous L D hL hD) n K) (z : ℝ) :
    HasDerivAt E.meanKinkBase ((L - 2 * z) / (2 * D)) z := by
  convert (((hasDerivAt_const z (D * (E.state L + E.state 0) - L ^ 2 / 2)).sub
    ((hasDerivAt_id z).pow 2)).add ((hasDerivAt_id z).const_mul L)).div_const (2 * D) using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

theorem IntervalDesign.meanKinkBase_curvature
    (E : IntervalDesign (homogeneous L D hL hD) n K) (z : ℝ) :
    deriv (deriv E.meanKinkBase) z = -1 / D := by
  have he : deriv E.meanKinkBase = fun y => (L - 2 * y) / (2 * D) :=
    funext (fun y => (E.meanKinkBase_hasDerivAt y).deriv)
  rw [he]
  have hd : HasDerivAt (fun y : ℝ => (L - 2 * y) / (2 * D)) (-2 / (2 * D)) z := by
    convert ((hasDerivAt_const z L).sub ((hasDerivAt_id z).const_mul 2)).div_const (2 * D) using 1 <;>
      first | rfl | ring
  rw [hd.deriv]
  field_simp [ne_of_gt hD]

theorem IntervalDesign.meanKinkCoefficient_reaction
    (E : IntervalDesign (homogeneous L D hL hD) n K) (i : Fin n) :
    2 * D * E.meanKinkCoefficient i = E.strength i * E.state (E.geometry.site i) := by
  unfold IntervalDesign.meanKinkCoefficient
  field_simp [ne_of_gt hD]

theorem IntervalDesign.meanKinkCoefficient_sum
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    (∑ i, E.meanKinkCoefficient i) = L / (2 * D) := by
  unfold IntervalDesign.meanKinkCoefficient
  rw [← Finset.sum_div, E.equation.conservation, E.homogeneous_source, homogeneous_mass]

end TimeTraps.Interval

end
