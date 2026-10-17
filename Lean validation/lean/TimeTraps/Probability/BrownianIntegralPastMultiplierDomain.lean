module

public import TimeTraps.Probability.BrownianIntegralPastMultiplierElementary

@[expose] public section

/-! A bounded raw-F_s variable acts on the actual closed future integrand
subspace. The coefficient is its pointwise product with the original
integrand; membership follows by closure of the elementary product rule. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
variable {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}
variable {Z : Ω → ℝ} {M : ℝ≥0} {s : ℝ≥0}

def brownianPastMultiplierAmbient
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) :
    brownianIntegralSpace B hBm P →L[ℝ] Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
  (brownianPastMultiplierL2
    ((hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable.comp measurable_snd)
    (fun p : ℝ × Ω => hb p.2)).comp (brownianIntegralSpace B hBm P).subtypeL

theorem brownianPastMultiplier_mem_space
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) (f : brownianIntegralSpace B hBm P)
    (hf : f ∈ brownianIntegralFutureSpace B hBm P s) :
    brownianPastMultiplierAmbient hZ hb f ∈ brownianIntegralSpace B hBm P := by
  let A := brownianPastMultiplierAmbient (P := P) hZ hb
  have hs : Submodule.span ℝ (Set.range
      (fun a : {a : BrownianIntegralElementary B hBm P // s ≤ a.left} =>
        brownianIntegralGenerator a.1)) ≤ (brownianIntegralSpace B hBm P).comap A.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change brownianPastMultiplierL2
      ((hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable.comp measurable_snd)
      (fun p : ℝ × Ω => hb p.2) a.1.processL2 ∈ brownianIntegralSpace B hBm P
    rw [brownianPastMultiplier_elementary a.1 a.2 hZ hb]
    exact (brownianIntegralGenerator (a.1.pastProduct a.2 hZ hb)).property
  have hc : IsClosed ((brownianIntegralSpace B hBm P).comap A.toLinearMap :
      Set (brownianIntegralSpace B hBm P)) :=
    (Submodule.isClosed_topologicalClosure (brownianIntegralStepSpace B hBm P)).preimage A.continuous
  exact Submodule.topologicalClosure_minimal _ hs hc hf

def brownianPastMultiplier
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) :
    brownianIntegralFutureSpace B hBm P s →L[ℝ] brownianIntegralSpace B hBm P :=
  ((brownianPastMultiplierAmbient hZ hb).comp
    (brownianIntegralFutureSpace B hBm P s).subtypeL).codRestrict
      (brownianIntegralSpace B hBm P)
      (fun f => brownianPastMultiplier_mem_space hZ hb f.val f.property)

theorem brownianPastMultiplier_coe
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) (f : brownianIntegralFutureSpace B hBm P s) :
    (brownianPastMultiplier hZ hb f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => Z p.2 * (f.val : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p) := by
  change brownianPastMultiplierL2
    ((hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable.comp measurable_snd)
    (fun p : ℝ × Ω => hb p.2) (f.val : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] _
  exact brownianPastMultiplierL2_coe _ _ _

theorem brownianPastMultiplier_norm
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) (f : brownianIntegralFutureSpace B hBm P s) :
    ‖brownianPastMultiplier hZ hb f‖ ≤ M.val * ‖f‖ := by
  change ‖brownianPastMultiplierL2
    ((hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable.comp measurable_snd)
    (fun p : ℝ × Ω => hb p.2) (f.val : Lp ℝ 2 ((volume : Measure ℝ).prod P))‖ ≤
      M.val * ‖(f.val : Lp ℝ 2 ((volume : Measure ℝ).prod P))‖
  exact brownianPastMultiplierL2_norm _ _ _

theorem brownianPastMultiplier_generator
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) (a : BrownianIntegralElementary B hBm P) (ha : s ≤ a.left) :
    brownianPastMultiplier hZ hb ⟨brownianIntegralGenerator a,
      brownianIntegralGenerator_mem_future a ha⟩ = brownianIntegralGenerator (a.pastProduct ha hZ hb) := by
  apply Subtype.ext
  change brownianPastMultiplierL2
    ((hZ.mono ((brownianNaturalFiltration B hBm).le s)).measurable.comp measurable_snd)
    (fun p : ℝ × Ω => hb p.2) a.processL2 = (a.pastProduct ha hZ hb).processL2
  exact brownianPastMultiplier_elementary a ha hZ hb

end TimeTraps.Probability

end
