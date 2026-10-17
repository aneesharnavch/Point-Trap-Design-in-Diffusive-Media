module

public import TimeTraps.Probability.BrownianIntegralClosure

@[expose] public section

/-! Inserting a deterministic time inside an elementary interval preserves
the actual process and its integral. The right subinterval retains the same
coefficient, whose adaptedness follows from filtration monotonicity. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

theorem brownianElementaryProcess_split {s u t : ℝ≥0} (hsu : s ≤ u) (hut : u ≤ t)
    (ξ : Ω → ℝ) (p : ℝ × Ω) :
    brownianElementaryProcess s t ξ p =
      brownianElementaryProcess s u ξ p + brownianElementaryProcess u t ξ p := by
  unfold brownianElementaryProcess brownianIntervalIndicator
  rw [← Ioc_union_Ioc_eq_Ioc (show s.val ≤ u.val from hsu) (show u.val ≤ t.val from hut),
    Set.indicator_union_of_disjoint (Ioc_disjoint_Ioc_of_le (le_refl u.val))]
  simp only [add_mul]

def BrownianIntegralElementary.refineLeft (a : BrownianIntegralElementary B hBm P)
    (u : ℝ≥0) (hsu : a.left ≤ u) : BrownianIntegralElementary B hBm P :=
  { a with right := u, ordered := hsu }

def BrownianIntegralElementary.refineRight (a : BrownianIntegralElementary B hBm P)
    (u : ℝ≥0) (hsu : a.left ≤ u) (hut : u ≤ a.right) : BrownianIntegralElementary B hBm P :=
  { a with
    left := u
    ordered := hut
    adapted := a.adapted.mono ((brownianNaturalFiltration B hBm).mono hsu) }

theorem brownianIntegralGenerator_refinement (a : BrownianIntegralElementary B hBm P)
    (u : ℝ≥0) (hsu : a.left ≤ u) (hut : u ≤ a.right) :
    brownianIntegralGenerator a = brownianIntegralGenerator (a.refineLeft u hsu) +
      brownianIntegralGenerator (a.refineRight u hsu hut) := by
  apply Subtype.ext
  change a.processL2 = (a.refineLeft u hsu).processL2 + (a.refineRight u hsu hut).processL2
  apply Lp.ext
  filter_upwards [a.processL2_coe, (a.refineLeft u hsu).processL2_coe,
    (a.refineRight u hsu hut).processL2_coe,
    Lp.coeFn_add (a.refineLeft u hsu).processL2 (a.refineRight u hsu hut).processL2]
    with p ha hl hr hadd
  change a.processL2 p =
    ((a.refineLeft u hsu).processL2 + (a.refineRight u hsu hut).processL2) p
  rw [hadd]
  change a.processL2 p = (a.refineLeft u hsu).processL2 p + (a.refineRight u hsu hut).processL2 p
  rw [ha, hl, hr]
  exact brownianElementaryProcess_split hsu hut a.coefficient p

theorem brownianIntegral_refinement (hB : IsPreBrownianReal B P)
    (a : BrownianIntegralElementary B hBm P) (u : ℝ≥0)
    (hsu : a.left ≤ u) (hut : u ≤ a.right) :
    brownianIntegral hB (brownianIntegralGenerator a) =
      brownianIntegral hB (brownianIntegralGenerator (a.refineLeft u hsu)) +
      brownianIntegral hB (brownianIntegralGenerator (a.refineRight u hsu hut)) := by
  rw [brownianIntegralGenerator_refinement a u hsu hut, map_add]

end TimeTraps.Probability

end
