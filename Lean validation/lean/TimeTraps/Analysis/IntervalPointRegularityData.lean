module

public import TimeTraps.Analysis.IntervalPointRegularityRepresentative

@[expose] public section

/-! An interval H2 certificate retaining both the actual AC state and its
AC/L2 slope representative.  Its consequences include all interior tests,
classical interior first derivatives, and both one-sided slope traces. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

structure IntervalSlopeRegularity (u v g : ℝ → ℝ) (l r : ℝ) : Prop where
  state_energy : IntervalEnergy u l r
  slope_energy : IntervalEnergy v l r
  slope_ae : deriv u =ᵐ[volume.restrict (Ioo l r)] v
  second_ae : deriv v =ᵐ[volume.restrict (Ioo l r)] g

theorem IntervalSlopeRegularity.weak_second {u v g : ℝ → ℝ} {l r : ℝ}
    (h : IntervalSlopeRegularity u v g l r) (hlr : l ≤ r) :
    IntervalWeakDerivative (deriv u) g l r :=
  (h.slope_energy.weakDerivative hlr).congr_ae h.slope_ae.symm h.second_ae

theorem IntervalSlopeRegularity.hasDerivAt {u v g : ℝ → ℝ} {l r : ℝ}
    (h : IntervalSlopeRegularity u v g l r) {x : ℝ} (hx : x ∈ Ioo l r) :
    HasDerivAt u (v x) x :=
  intervalEnergy_hasDerivAt_of_ae_deriv h.state_energy
    (by simpa only [uIcc_of_le (hx.1.trans hx.2).le] using h.slope_energy.continuousOn) h.slope_ae hx

theorem IntervalSlopeRegularity.second_derivative_ae {u v g : ℝ → ℝ} {l r : ℝ}
    (h : IntervalSlopeRegularity u v g l r) :
    deriv (deriv u) =ᵐ[volume.restrict (Ioo l r)] g := by
  have he : EqOn (deriv u) v (Ioo l r) := fun _ hx => (h.hasDerivAt hx).deriv
  have hd := he.deriv isOpen_Ioo
  filter_upwards [ae_restrict_mem measurableSet_Ioo, h.second_ae] with x hx hg
  exact (hd hx).trans hg

theorem IntervalSlopeRegularity.left_trace {u v g : ℝ → ℝ} {l r : ℝ}
    (h : IntervalSlopeRegularity u v g l r) (hlr : l < r) :
    Tendsto (deriv u) (𝓝[>] l) (𝓝 (v l)) :=
  intervalEnergy_deriv_left_trace h.state_energy hlr
    (by simpa only [uIcc_of_le hlr.le] using h.slope_energy.continuousOn) h.slope_ae

theorem IntervalSlopeRegularity.right_trace {u v g : ℝ → ℝ} {l r : ℝ}
    (h : IntervalSlopeRegularity u v g l r) (hlr : l < r) :
    Tendsto (deriv u) (𝓝[<] r) (𝓝 (v r)) :=
  intervalEnergy_deriv_right_trace h.state_energy hlr
    (by simpa only [uIcc_of_le hlr.le] using h.slope_energy.continuousOn) h.slope_ae

end TimeTraps.Analysis
