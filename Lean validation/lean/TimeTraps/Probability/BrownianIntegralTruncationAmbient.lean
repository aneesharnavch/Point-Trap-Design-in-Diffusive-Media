module

public import TimeTraps.Probability.BrownianIntegralClosure

@[expose] public section

/-! Multiplication by the deterministic time cutoff on the actual product
L² space is a linear contraction. No filtration or completion assumption
is needed for this ambient operator. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def brownianTimePast (t : ℝ≥0) : Set (ℝ × Ω) := {p | p.1 ≤ t.val}

theorem brownianTimePast_measurable (t : ℝ≥0) : MeasurableSet (brownianTimePast (Ω := Ω) t) :=
  measurableSet_le measurable_fst measurable_const

def brownianTimeCutoffValue (P : Measure Ω) (t : ℝ≥0)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) : Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
  ((Lp.memLp f).indicator (brownianTimePast_measurable t)).toLp
    ((brownianTimePast t).indicator f)

theorem brownianTimeCutoffValue_coe (P : Measure Ω) (t : ℝ≥0)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    brownianTimeCutoffValue P t f =ᵐ[volume.prod P] (brownianTimePast t).indicator f :=
  ((Lp.memLp f).indicator (brownianTimePast_measurable t)).coeFn_toLp

theorem brownianTimeCutoffValue_add (P : Measure Ω) (t : ℝ≥0)
    (f g : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    brownianTimeCutoffValue P t (f + g) = brownianTimeCutoffValue P t f +
      brownianTimeCutoffValue P t g := by
  apply Lp.ext
  filter_upwards [brownianTimeCutoffValue_coe P t (f + g),
    brownianTimeCutoffValue_coe P t f, brownianTimeCutoffValue_coe P t g,
    Lp.coeFn_add f g, Lp.coeFn_add (brownianTimeCutoffValue P t f) (brownianTimeCutoffValue P t g)]
    with p hsum hf hg hfg hout
  rw [hsum, hout]
  change (brownianTimePast t).indicator (⇑(f + g)) p =
    brownianTimeCutoffValue P t f p + brownianTimeCutoffValue P t g p
  rw [hf, hg]
  by_cases hp : p ∈ brownianTimePast t
  · simp only [indicator_of_mem hp]
    exact hfg
  · simp only [indicator_of_notMem hp, add_zero]

theorem brownianTimeCutoffValue_smul (P : Measure Ω) (t : ℝ≥0) (c : ℝ)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    brownianTimeCutoffValue P t (c • f) = c • brownianTimeCutoffValue P t f := by
  apply Lp.ext
  filter_upwards [brownianTimeCutoffValue_coe P t (c • f),
    brownianTimeCutoffValue_coe P t f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (brownianTimeCutoffValue P t f)] with p hcut hf hcf hout
  rw [hcut, hout]
  change (brownianTimePast t).indicator (⇑(c • f)) p = c • brownianTimeCutoffValue P t f p
  rw [hf]
  by_cases hp : p ∈ brownianTimePast t
  · simp only [indicator_of_mem hp]
    exact hcf
  · simp only [indicator_of_notMem hp, smul_zero]

theorem brownianTimeCutoffValue_norm_le (P : Measure Ω) (t : ℝ≥0)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) : ‖brownianTimeCutoffValue P t f‖ ≤ ‖f‖ := by
  rw [brownianTimeCutoffValue, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_indicator_le f)

def brownianTimeCutoffLinear (P : Measure Ω) (t : ℝ≥0) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P) →ₗ[ℝ] Lp ℝ 2 ((volume : Measure ℝ).prod P) where
  toFun := brownianTimeCutoffValue P t
  map_add' := brownianTimeCutoffValue_add P t
  map_smul' := brownianTimeCutoffValue_smul P t

def brownianTimeCutoffAmbient (P : Measure Ω) (t : ℝ≥0) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P) →L[ℝ] Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
  (brownianTimeCutoffLinear P t).mkContinuous 1 (fun f => by
    change ‖brownianTimeCutoffValue P t f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using brownianTimeCutoffValue_norm_le P t f)

theorem brownianTimeCutoffAmbient_coe (P : Measure Ω) (t : ℝ≥0)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    brownianTimeCutoffAmbient P t f =ᵐ[volume.prod P] (brownianTimePast t).indicator f :=
  brownianTimeCutoffValue_coe P t f

theorem brownianTimeCutoffAmbient_norm_le (P : Measure Ω) (t : ℝ≥0)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) : ‖brownianTimeCutoffAmbient P t f‖ ≤ ‖f‖ :=
  brownianTimeCutoffValue_norm_le P t f

end TimeTraps.Probability

end
