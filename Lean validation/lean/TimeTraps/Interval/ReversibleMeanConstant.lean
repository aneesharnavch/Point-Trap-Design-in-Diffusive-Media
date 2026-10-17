module

public import TimeTraps.Interval.SourceMeanConstant
public import TimeTraps.Interval.ReversibleMeanAttainment

@[expose] public section

/-! If conductance times stationary density is constant, the physical
mean optimizer has equal strengths and stationary-quantile midpoints. -/

namespace TimeTraps.Interval

open Set MeasureTheory

variable {n : ℕ} {K c : ℝ} {a π : ℝ → ℝ}
  {ha : ContinuousOn a (Icc (0 : ℝ) 1)} {hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x}
  {hπ : ContinuousOn π (Icc (0 : ℝ) 1)} {hπpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < π x}

theorem reversibleUnitMedium_weight_constant (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (hc : ∀ x ∈ Icc (0 : ℝ) 1, a x * π x = c) (z : ℝ) :
    (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight.value z = 1 / c := by
  rw [reversibleUnitMedium_weight hπmass, hc _
    ((reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse_mem z)]

theorem reversible_mean_constant_minimum (hn : 0 < n) (hK : 0 < K) (hcpos : 0 < c)
    (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (hc : ∀ x ∈ Icc (0 : ℝ) 1, a x * π x = c) :
    IsLeast (range (fun E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K =>
      reversibleMeanCost π E.state)) (1 / K + 1 / (12 * c * (n : ℝ) ^ 2)) := by
  have h := source_mean_constant_minimum (A := reversibleUnitMedium a π ha hapos hπ hπpos)
    hn hK (one_div_pos.mpr hcpos) (fun z _ => reversibleUnitMedium_weight_constant hπmass hc z)
  have he : (fun E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K =>
      E.sourceMeanCost) = (fun E => reversibleMeanCost π E.state) :=
    funext (reversible_mean_objective hπmass)
  rw [he, reversibleUnitMedium_mass hπmass] at h
  convert h using 1
  ring

theorem reversible_mean_constant_reconstruction (hn : 0 < n) (hK : 0 < K) (hcpos : 0 < c)
    (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (hc : ∀ x ∈ Icc (0 : ℝ) 1, a x * π x = c) :
    ∃ E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K,
      (∀ i, E.strength i = K / (n : ℝ)) ∧
      (∀ i, E.geometry.site i = (reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse
        ((2 * (i.val : ℝ) + 1) / (2 * (n : ℝ)))) ∧
      reversibleMeanCost π E.state = 1 / K + 1 / (12 * c * (n : ℝ) ^ 2) := by
  obtain ⟨E, hk, hx, he⟩ := source_mean_constant_reconstruction
    (A := reversibleUnitMedium a π ha hapos hπ hπpos) hn hK (one_div_pos.mpr hcpos)
    (fun z _ => reversibleUnitMedium_weight_constant hπmass hc z)
  refine ⟨E, hk, hx, ?_⟩
  rw [reversible_mean_objective hπmass, reversibleUnitMedium_mass hπmass] at he
  rw [he]
  ring

theorem reversible_mean_constant_optimal_iff (hK : 0 < K) (hcpos : 0 < c)
    (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (hc : ∀ x ∈ Icc (0 : ℝ) 1, a x * π x = c)
    (E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K) :
    (∀ F : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K,
      reversibleMeanCost π E.state ≤ reversibleMeanCost π F.state) ↔
      (∀ i, E.strength i = K / (n : ℝ)) ∧
      (∀ i, E.geometry.site i = (reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse
        ((2 * (i.val : ℝ) + 1) / (2 * (n : ℝ)))) := by
  have h := source_mean_constant_optimal_iff hK (one_div_pos.mpr hcpos)
    (fun z _ => reversibleUnitMedium_weight_constant hπmass hc z) E
  unfold IntervalDesign.SourceMeanOptimal at h
  simpa only [reversible_mean_objective hπmass] using h

theorem reversible_mean_constant_eq_iff (hK : 0 < K) (hcpos : 0 < c)
    (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (hc : ∀ x ∈ Icc (0 : ℝ) 1, a x * π x = c)
    (E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K) :
    reversibleMeanCost π E.state = 1 / K + 1 / (12 * c * (n : ℝ) ^ 2) ↔
      (∀ i, E.strength i = K / (n : ℝ)) ∧
      (∀ i, E.geometry.site i = (reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse
        ((2 * (i.val : ℝ) + 1) / (2 * (n : ℝ)))) := by
  have h := source_mean_constant_eq_iff hK (one_div_pos.mpr hcpos)
    (fun z _ => reversibleUnitMedium_weight_constant hπmass hc z) E
  rw [reversible_mean_objective hπmass, reversibleUnitMedium_mass hπmass] at h
  convert h using 2
  ring

end TimeTraps.Interval
