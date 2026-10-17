module

public import TimeTraps.Spectral.CapacityRoot
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! The positive root of z tan z = a, with its exact weak and strong limits.
The value at nonpositive a is set to zero solely to provide a real-domain
function; every spectral identification below uses a strictly positive a. -/

namespace TimeTraps.Spectral

open Set Filter Topology

theorem positive_budget_phase_exists {a : ℝ} (ha : 0 < a) :
    ∃ z : ℝ, 0 < z ∧ z = Real.arctan (a / z) := by
  obtain ⟨z, hz, _⟩ := capacity_root_existsUnique {()}
    (Finset.singleton_nonempty ()) (fun _ : Unit => a)
    (fun _ _ => ha) (L := 2) (by norm_num)
  refine ⟨z, hz.1, ?_⟩
  have he := hz.2
  simp only [phaseCapacity, Finset.sum_singleton] at he
  linarith

noncomputable def budgetPhase (a : ℝ) : ℝ :=
  if ha : 0 < a then
    Classical.choose (positive_budget_phase_exists ha)
  else 0

theorem budgetPhase_spec {a : ℝ} (ha : 0 < a) :
    0 < budgetPhase a ∧ budgetPhase a = Real.arctan (a / budgetPhase a) := by
  simp only [budgetPhase, dif_pos ha]
  exact Classical.choose_spec (positive_budget_phase_exists ha)

theorem budgetPhase_pos {a : ℝ} (ha : 0 < a) : 0 < budgetPhase a := by
  exact (budgetPhase_spec ha).1

theorem budgetPhase_nonneg (a : ℝ) : 0 ≤ budgetPhase a := by
  by_cases ha : 0 < a
  · exact (budgetPhase_pos ha).le
  · simp [budgetPhase, ha]

theorem budgetPhase_lt_pi_div_two (a : ℝ) : budgetPhase a < Real.pi / 2 := by
  by_cases ha : 0 < a
  · rw [(budgetPhase_spec ha).2]
    exact Real.arctan_lt_pi_div_two _
  · simp only [budgetPhase, dif_neg ha]
    exact half_pos Real.pi_pos

theorem budgetPhase_equation {a : ℝ} (ha : 0 < a) :
    budgetPhase a * Real.tan (budgetPhase a) = a := by
  have he : Real.tan (budgetPhase a) = a / budgetPhase a := by
    simpa only [Real.tan_arctan] using congrArg Real.tan (budgetPhase_spec ha).2
  rw [he, mul_div_cancel₀ _ (ne_of_gt (budgetPhase_pos ha))]

theorem phaseProduct_strictMonoOn :
    StrictMonoOn (fun z : ℝ => z * Real.tan z) (Ioo 0 (Real.pi / 2)) := by
  intro a ha b hb hab
  have htan := Real.strictMonoOn_tan
    ⟨by linarith [Real.pi_pos, ha.1], ha.2⟩
    ⟨by linarith [Real.pi_pos, hb.1], hb.2⟩ hab
  exact mul_lt_mul hab htan.le (Real.tan_pos_of_pos_of_lt_pi_div_two ha.1 ha.2) hb.1.le

theorem budgetPhase_sq_lt {a : ℝ} (ha : 0 < a) : (budgetPhase a) ^ 2 < a := by
  calc
    budgetPhase a ^ 2 < budgetPhase a * Real.tan (budgetPhase a) := by
      rw [pow_two]
      exact mul_lt_mul_of_pos_left
        (Real.lt_tan (budgetPhase_pos ha) (budgetPhase_lt_pi_div_two a)) (budgetPhase_pos ha)
    _ = a := budgetPhase_equation ha

theorem budgetPhase_eq_of_equation {a z : ℝ} (ha : 0 < a)
    (hz : z ∈ Ioo 0 (Real.pi / 2)) (he : z * Real.tan z = a) :
    z = budgetPhase a :=
  phaseProduct_strictMonoOn.injOn hz
    ⟨budgetPhase_pos ha, budgetPhase_lt_pi_div_two a⟩ (he.trans (budgetPhase_equation ha).symm)

theorem budgetPhase_strictMonoOn : StrictMonoOn budgetPhase (Ioi 0) := by
  intro a ha b hb hab
  by_contra h
  have hle := phaseProduct_strictMonoOn.monotoneOn
    ⟨budgetPhase_pos hb, budgetPhase_lt_pi_div_two b⟩
    ⟨budgetPhase_pos ha, budgetPhase_lt_pi_div_two a⟩ (le_of_not_gt h)
  rw [budgetPhase_equation ha, budgetPhase_equation hb] at hle
  exact (not_le_of_gt hab) hle

theorem budgetPhase_tendsto_zero : Tendsto budgetPhase (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Eventually.of_forall (fun a => hc.trans_le (budgetPhase_nonneg a))
  · intro c hc
    have he : ∀ᶠ a : ℝ in 𝓝[>] 0, a < c ^ 2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (sq_pos_of_pos hc))
    filter_upwards [self_mem_nhdsWithin, he] with a ha hbound
    have hs := budgetPhase_sq_lt ha
    nlinarith [budgetPhase_nonneg a]

theorem budgetPhase_tendsto_atTop : Tendsto budgetPhase atTop (𝓝 (Real.pi / 2)) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    let b : ℝ := (max c 0 + Real.pi / 2) / 2
    have hb : b ∈ Ioo 0 (Real.pi / 2) := by
      have hm : max c 0 < Real.pi / 2 := max_lt hc (half_pos Real.pi_pos)
      have hm0 := le_max_right c (0 : ℝ)
      dsimp [b]
      constructor <;> linarith [Real.pi_pos]
    have hcb : c < b := by
      have hm := le_max_left c (0 : ℝ)
      dsimp [b]
      linarith
    have hprod : 0 < b * Real.tan b :=
      mul_pos hb.1 (Real.tan_pos_of_pos_of_lt_pi_div_two hb.1 hb.2)
    filter_upwards [eventually_gt_atTop (b * Real.tan b)] with a ha
    have ha0 : 0 < a := hprod.trans ha
    apply hcb.trans
    by_contra h
    have hle := phaseProduct_strictMonoOn.monotoneOn
      ⟨budgetPhase_pos ha0, budgetPhase_lt_pi_div_two a⟩ hb (le_of_not_gt h)
    rw [budgetPhase_equation ha0] at hle
    exact (not_le_of_gt ha) hle
  · intro c hc
    exact Eventually.of_forall (fun a => (budgetPhase_lt_pi_div_two a).trans hc)

theorem budgetPhase_tendsto_zero_within : Tendsto budgetPhase (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨budgetPhase_tendsto_zero, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact budgetPhase_pos ha

theorem tan_div_self_tendsto_zero_right :
    Tendsto (fun z : ℝ => Real.tan z / z) (𝓝[>] 0) (𝓝 1) := by
  have hd := (Real.hasDerivAt_tan (x := 0) (by simp)).tendsto_slope_zero_right
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd

/-- The dimensionless optimum is asymptotic to its budget parameter. -/
theorem budgetPhase_sq_div_tendsto_zero :
    Tendsto (fun a : ℝ => budgetPhase a ^ 2 / a) (𝓝[>] 0) (𝓝 1) := by
  have ht := tan_div_self_tendsto_zero_right.comp budgetPhase_tendsto_zero_within
  have hi := ht.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply (show Tendsto (fun a : ℝ => (Real.tan (budgetPhase a) / budgetPhase a)⁻¹)
    (𝓝[>] 0) (𝓝 1) by simpa using hi).congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  change 0 < a at ha
  have he := budgetPhase_equation ha
  field_simp [ne_of_gt ha, ne_of_gt (budgetPhase_pos ha),
    ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two
      (budgetPhase_pos ha) (budgetPhase_lt_pi_div_two a))]
  nlinarith [he]

end TimeTraps.Spectral
