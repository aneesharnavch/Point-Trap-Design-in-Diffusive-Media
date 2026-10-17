module

public import TimeTraps.Analysis.PositiveTimeChangeCompact
public import TimeTraps.Probability.ReflectedFoldTrajectory

@[expose] public section

/-! Literal integral clocks along confined reflected paths. The clock
and inverse are defined independently of a path-regularity proof. On a
continuous path, the positive compact spatial speed gives their exact
inverse identities and quantitative bounds. -/

namespace TimeTraps.Probability

open Set Filter TimeTraps.Analysis
open scoped NNReal Topology

variable {Ω : Type*}

noncomputable def reflectedPositiveTimeClock (L D x : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (c : ℝ → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  Real.toNNReal (∫ r in (0 : ℝ)..s.val, c (foldedTrajectory L D x B r.toNNReal ω))

noncomputable def reflectedPositiveTimeInverse (L D x : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (c : ℝ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  Function.invFun (fun s => reflectedPositiveTimeClock L D x B c s ω) t

noncomputable def reflectedPositiveTimeSpeed (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L))
    (hpos : ∀ y ∈ Icc 0 L, 0 < c y) (ω : Ω) (hω : Continuous (fun s => B s ω)) :
    PositiveTimeSpeed := by
  letI : Nonempty (Icc (0 : ℝ) L) := ⟨⟨0, le_rfl, hL.le⟩⟩
  let Y : ℝ≥0 → Icc (0 : ℝ) L :=
    fun s => ⟨foldedTrajectory L D x B s ω, foldedTrajectory_mem L hL D x B s ω⟩
  have hY : Continuous Y :=
    ((reflectedFold_continuous L).comp
      (continuous_const.add (continuous_const.mul hω))).subtype_mk _
  exact PositiveTimeSpeed.ofCompact (fun y : Icc (0 : ℝ) L => c y.val) hc.domRestrict
    (fun y => hpos y.val y.property) Y hY

theorem reflectedPositiveTimeSpeed_rate (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L))
    (hpos : ∀ y ∈ Icc 0 L, 0 < c y) (ω : Ω) (hω : Continuous (fun s => B s ω)) (s : ℝ≥0) :
    (reflectedPositiveTimeSpeed L hL D x B c hc hpos ω hω).rate s =
      c (foldedTrajectory L D x B s ω) := rfl

theorem reflectedPositiveTimeSpeed_extrema (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L))
    (hpos : ∀ y ∈ Icc 0 L, 0 < c y) (ω : Ω) (hω : Continuous (fun s => B s ω)) :
    let v := reflectedPositiveTimeSpeed L hL D x B c hc hpos ω hω
    (∃ y ∈ Icc 0 L, c y = (v.lower : ℝ) ∧ ∀ z ∈ Icc 0 L, c y ≤ c z) ∧
      (∃ y ∈ Icc 0 L, c y = (v.upper : ℝ) ∧ ∀ z ∈ Icc 0 L, c z ≤ c y) := by
  let : Nonempty (Icc (0 : ℝ) L) := ⟨⟨0, le_rfl, hL.le⟩⟩
  let Y : ℝ≥0 → Icc (0 : ℝ) L :=
    fun s => ⟨foldedTrajectory L D x B s ω, foldedTrajectory_mem L hL D x B s ω⟩
  have hY : Continuous Y :=
    ((reflectedFold_continuous L).comp
      (continuous_const.add (continuous_const.mul hω))).subtype_mk _
  obtain ⟨ymin, hmin, hminle⟩ := PositiveTimeSpeed.ofCompact_lower_minimum
    (fun y : Icc (0 : ℝ) L => c y.val) hc.domRestrict (fun y => hpos y.val y.property) Y hY
  obtain ⟨ymax, hmax, hlemax⟩ := PositiveTimeSpeed.ofCompact_upper_maximum
    (fun y : Icc (0 : ℝ) L => c y.val) hc.domRestrict (fun y => hpos y.val y.property) Y hY
  exact ⟨⟨ymin.val, ymin.property, hmin, fun z hz => hminle ⟨z, hz⟩⟩,
    ⟨ymax.val, ymax.property, hmax, fun z hz => hlemax ⟨z, hz⟩⟩⟩

theorem reflectedPositiveTimeClock_coe (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (c : ℝ → ℝ) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (s : ℝ≥0) (ω : Ω) :
    (reflectedPositiveTimeClock L D x B c s ω : ℝ) =
      ∫ r in (0 : ℝ)..s.val, c (foldedTrajectory L D x B r.toNNReal ω) := by
  exact Real.coe_toNNReal _ (intervalIntegral.integral_nonneg_of_forall s.coe_nonneg
    (fun r => (hpos _ (foldedTrajectory_mem L hL D x B r.toNNReal ω)).le))

theorem reflectedPositiveTimeClock_eq (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L))
    (hpos : ∀ y ∈ Icc 0 L, 0 < c y) (ω : Ω) (hω : Continuous (fun s => B s ω)) :
    (fun s => reflectedPositiveTimeClock L D x B c s ω) =
      (reflectedPositiveTimeSpeed L hL D x B c hc hpos ω hω).clock := by
  funext s
  apply NNReal.eq
  rw [reflectedPositiveTimeClock_coe L hL D x B c hpos, PositiveTimeSpeed.clock_coe]
  rfl

theorem reflectedPositiveTimeInverse_eq (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L))
    (hpos : ∀ y ∈ Icc 0 L, 0 < c y) (ω : Ω) (hω : Continuous (fun s => B s ω)) :
    (fun t => reflectedPositiveTimeInverse L D x B c t ω) =
      (reflectedPositiveTimeSpeed L hL D x B c hc hpos ω hω).inverse := by
  change Function.invFun (fun s => reflectedPositiveTimeClock L D x B c s ω) = _
  rw [reflectedPositiveTimeClock_eq L hL D x B c hc hpos ω hω]
  exact Function.invFun_eq_of_injective_of_rightInverse
    (PositiveTimeSpeed.clock_strictMono _).injective (PositiveTimeSpeed.clock_inverse _)

theorem reflectedPositiveTimeChange_regular (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L))
    (hpos : ∀ y ∈ Icc 0 L, 0 < c y) (ω : Ω) (hω : Continuous (fun s => B s ω)) :
    Continuous (fun s => reflectedPositiveTimeClock L D x B c s ω) ∧
    StrictMono (fun s => reflectedPositiveTimeClock L D x B c s ω) ∧
    Tendsto (fun s => reflectedPositiveTimeClock L D x B c s ω) atTop atTop ∧
    Continuous (fun t => reflectedPositiveTimeInverse L D x B c t ω) ∧
    StrictMono (fun t => reflectedPositiveTimeInverse L D x B c t ω) ∧
    ∀ t, reflectedPositiveTimeClock L D x B c (reflectedPositiveTimeInverse L D x B c t ω) ω = t ∧
      reflectedPositiveTimeInverse L D x B c (reflectedPositiveTimeClock L D x B c t ω) ω = t := by
  let v := reflectedPositiveTimeSpeed L hL D x B c hc hpos ω hω
  have heC := reflectedPositiveTimeClock_eq L hL D x B c hc hpos ω hω
  have heI := reflectedPositiveTimeInverse_eq L hL D x B c hc hpos ω hω
  have hC (s : ℝ≥0) := congrFun heC s
  have hI (s : ℝ≥0) := congrFun heI s
  refine ⟨heC.symm ▸ v.clock_continuous, heC.symm ▸ v.clock_strictMono,
    heC.symm ▸ v.clock_tendsto, heI.symm ▸ v.inverse_continuous,
    heI.symm ▸ v.inverse_strictMono, fun t => ?_⟩
  constructor
  · rw [hC, hI]
    exact v.clock_inverse t
  · rw [hI, hC]
    exact v.inverse_clock t

theorem reflectedPositiveTimeChange_bounds (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L))
    (hpos : ∀ y ∈ Icc 0 L, 0 < c y) (ω : Ω) (hω : Continuous (fun s => B s ω)) (t : ℝ≥0) :
    let v := reflectedPositiveTimeSpeed L hL D x B c hc hpos ω hω
    v.lower * t ≤ reflectedPositiveTimeClock L D x B c t ω ∧
      reflectedPositiveTimeClock L D x B c t ω ≤ v.upper * t ∧
      t / v.upper ≤ reflectedPositiveTimeInverse L D x B c t ω ∧
      reflectedPositiveTimeInverse L D x B c t ω ≤ t / v.lower := by
  dsimp only
  rw [congrFun (reflectedPositiveTimeClock_eq L hL D x B c hc hpos ω hω) t,
    congrFun (reflectedPositiveTimeInverse_eq L hL D x B c hc hpos ω hω) t]
  exact ⟨(PositiveTimeSpeed.clock_bounds _ t).1, (PositiveTimeSpeed.clock_bounds _ t).2,
    PositiveTimeSpeed.inverse_bounds _ t⟩

end TimeTraps.Probability
