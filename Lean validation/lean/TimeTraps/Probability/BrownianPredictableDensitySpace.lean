module

public import TimeTraps.Probability.BrownianPredictableDensityIndicator
public import TimeTraps.Probability.BrownianPredictableDensityL2Limit

@[expose] public section

/-! Membership in the existing integral space, stated using representatives.
This permits the measurable-set argument to use pointwise indicator identities
while its limits are taken in the actual product L2 space. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

def BrownianPredictableDensityMember (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) (P : Measure Ω) (f : ℝ × Ω → ℝ) : Prop :=
  ∃ g : Lp ℝ 2 (volume.prod P), g ∈ brownianIntegralSpace B hBm P ∧ g =ᵐ[volume.prod P] f

theorem brownianPredictableDensityMember_zero :
    BrownianPredictableDensityMember B hBm P 0 := by
  exact ⟨0, (brownianIntegralSpace B hBm P).zero_mem, Lp.coeFn_zero ℝ 2 (volume.prod P)⟩

theorem brownianPredictableDensityMember_congr {f g : ℝ × Ω → ℝ}
    (hf : BrownianPredictableDensityMember B hBm P f) (hfg : f =ᵐ[volume.prod P] g) :
    BrownianPredictableDensityMember B hBm P g := by
  obtain ⟨a, ha, haf⟩ := hf
  exact ⟨a, ha, haf.trans hfg⟩

theorem brownianPredictableDensityMember_add {f g : ℝ × Ω → ℝ}
    (hf : BrownianPredictableDensityMember B hBm P f)
    (hg : BrownianPredictableDensityMember B hBm P g) :
    BrownianPredictableDensityMember B hBm P (f + g) := by
  obtain ⟨a, ha, haf⟩ := hf
  obtain ⟨b, hb, hbg⟩ := hg
  refine ⟨a + b, (brownianIntegralSpace B hBm P).add_mem ha hb, ?_⟩
  exact (Lp.coeFn_add a b).trans (haf.add hbg)

theorem brownianPredictableDensityMember_sub {f g : ℝ × Ω → ℝ}
    (hf : BrownianPredictableDensityMember B hBm P f)
    (hg : BrownianPredictableDensityMember B hBm P g) :
    BrownianPredictableDensityMember B hBm P (f - g) := by
  obtain ⟨a, ha, haf⟩ := hf
  obtain ⟨b, hb, hbg⟩ := hg
  refine ⟨a - b, (brownianIntegralSpace B hBm P).sub_mem ha hb, ?_⟩
  exact (Lp.coeFn_sub a b).trans (haf.sub hbg)

theorem brownianPredictableDensityMember_smul {f : ℝ × Ω → ℝ}
    (hf : BrownianPredictableDensityMember B hBm P f) (c : ℝ) :
    BrownianPredictableDensityMember B hBm P (c • f) := by
  obtain ⟨a, ha, haf⟩ := hf
  exact ⟨c • a, (brownianIntegralSpace B hBm P).smul_mem c ha,
    (Lp.coeFn_smul c a).trans (haf.const_smul c)⟩

theorem brownianPredictableDensityMember_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ × Ω → ℝ)
    (hf : ∀ i ∈ s, BrownianPredictableDensityMember B hBm P (f i)) :
    BrownianPredictableDensityMember B hBm P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using brownianPredictableDensityMember_zero
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      exact brownianPredictableDensityMember_add (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem brownianPredictableDensityMember_memLp {f : ℝ × Ω → ℝ}
    (hf : BrownianPredictableDensityMember B hBm P f) : MemLp f 2 (volume.prod P) := by
  obtain ⟨a, _, haf⟩ := hf
  exact (memLp_congr_ae haf).mp (Lp.memLp a)

theorem brownianPredictableDensityMember_toLp {f : ℝ × Ω → ℝ}
    (hf : BrownianPredictableDensityMember B hBm P f) (hL : MemLp f 2 (volume.prod P)) :
    hL.toLp f ∈ brownianIntegralSpace B hBm P := by
  obtain ⟨a, ha, haf⟩ := hf
  have he : hL.toLp f = a := Lp.ext (hL.coeFn_toLp.trans haf.symm)
  exact he ▸ ha

theorem brownianPredictableDensityMember_limit {f : ℕ → ℝ × Ω → ℝ} {g H : ℝ × Ω → ℝ}
    (hf : ∀ n, BrownianPredictableDensityMember B hBm P (f n))
    (hg : MemLp g 2 (volume.prod P)) (hH : MemLp H 2 (volume.prod P))
    (hb : ∀ n, ∀ᵐ p ∂volume.prod P, |f n p| ≤ H p)
    (hgb : ∀ᵐ p ∂volume.prod P, |g p| ≤ H p)
    (hlim : ∀ᵐ p ∂volume.prod P, Tendsto (fun n => f n p) atTop (𝓝 (g p))) :
    BrownianPredictableDensityMember B hBm P g := by
  have hL := fun n => brownianPredictableDensityMember_memLp (hf n)
  refine ⟨hg.toLp g, ?_, hg.coeFn_toLp⟩
  exact (brownianIntegralStepSpace B hBm P).isClosed_topologicalClosure.mem_of_tendsto
    (brownianPredictableDensity_toLp_tendsto hL hg hH hb hgb hlim)
    (Filter.Eventually.of_forall (fun n => brownianPredictableDensityMember_toLp (hf n) (hL n)))

end TimeTraps.Probability
