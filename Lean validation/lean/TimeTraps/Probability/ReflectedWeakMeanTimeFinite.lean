module

public import TimeTraps.Interval.ReflectedMeanKinkBridge
public import TimeTraps.Probability.ReflectedFiniteKinkKilling

@[expose] public section

/-! The original full-H1 homogeneous weak mean state satisfies the
actual finite-time killed stochastic identity. Its quadratic-plus-kink
representation, reflection and reaction conditions are all deduced from
the weak equation. The stochastic term belongs to the original Brownian
integrand space and uses the literal local-time survival weight. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

def reflectedWeakMeanIntegrand (E : IntervalDesign (homogeneous L D hL hD) n K)
    (x : ℝ) (T : ℝ≥0) : BrownianIntegrand :=
  reflectedAtomicSurvivalMultiplier L hL D hD x E.geometry.site E.strength
    (fun i => (E.strength_pos i).le)
    (reflectedFiniteKinkC2Integrand E.meanKinkBase_contDiff L hL D hD E.geometry.site
      E.meanKinkCoefficient (fun i => by
        have hi := E.geometry.site_interior i
        rw [E.homogeneous_source] at hi
        exact hi) x T)

theorem reflectedWeakMeanTime_finite (E : IntervalDesign (homogeneous L D hL hD) n K)
    (x : ℝ) (T : ℝ≥0) :
    (fun ω => reflectedAtomicSurvival L D x E.geometry.site E.strength T ω *
      E.state (foldedTrajectory L D x brownianDyadicPath T ω) - E.state (reflectedFold L x))
      =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedWeakMeanIntegrand E x T) ω -
        ∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x E.geometry.site E.strength r.toNNReal ω) := by
  have ha (i : Fin n) : E.geometry.site i ∈ Ioo 0 L := by
    have hi := E.geometry.site_interior i
    rw [E.homogeneous_source] at hi
    exact hi
  have hsource (z : ℝ) (_hz : z ∈ Icc 0 L) : D * deriv (deriv E.meanKinkBase) z = -1 := by
    rw [E.meanKinkBase_curvature z]
    field_simp [ne_of_gt hD]
  have he := reflectedFiniteKinkC2_mean_time_formula E.meanKinkBase_contDiff L hL D hD
    E.geometry.site E.meanKinkCoefficient E.strength ha (fun i => (E.strength_pos i).le) x T
    E.meanKinkSlope_endpoints.1 E.meanKinkSlope_endpoints.2 E.meanKinkPotential_reaction hsource
  filter_upwards [he] with ω hω
  have hv : finiteKinkPotential E.meanKinkBase Finset.univ E.geometry.site E.meanKinkCoefficient
      (foldedTrajectory L D x brownianDyadicPath T ω) =
        E.state (foldedTrajectory L D x brownianDyadicPath T ω) :=
    E.meanKinkPotential_eq (foldedTrajectory_mem L hL D x brownianDyadicPath T ω)
  have hz : finiteKinkPotential E.meanKinkBase Finset.univ E.geometry.site E.meanKinkCoefficient
      (reflectedFold L x) = E.state (reflectedFold L x) :=
    E.meanKinkPotential_eq (reflectedFold_mem L hL x)
  rw [hv, hz] at hω
  exact hω

theorem reflectedWeakMeanTime_finite_at_start (E : IntervalDesign (homogeneous L D hL hD) n K)
    {x : ℝ} (hx : x ∈ Icc 0 L) (T : ℝ≥0) :
    (fun ω => reflectedAtomicSurvival L D x E.geometry.site E.strength T ω *
      E.state (foldedTrajectory L D x brownianDyadicPath T ω) - E.state x)
      =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedWeakMeanIntegrand E x T) ω -
        ∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x E.geometry.site E.strength r.toNNReal ω) := by
  simpa only [reflectedFold_eq_self L hL x hx] using reflectedWeakMeanTime_finite E x T

end TimeTraps.Probability

end
