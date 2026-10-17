module

public import TimeTraps.Probability.GraphOccupationL2Cauchy
public import TimeTraps.Probability.OccupationPotentialCauchyBound

@[expose] public section

/-! Uniform approximation of actual finite-time potentials implies a
genuine Cauchy sequence of occupation variables in the original path law.
The potential and square-moment identities are derived from the graph
semigroup, rather than assumed for abstract candidate random variables. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Probability TimeTraps.Graph
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupationPotential_add
    (P : GraphShiftedContactOperatorProblem V E)
    (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ) :
    P.occupationPotential (f + g) T = P.occupationPotential f T + P.occupationPotential g T := by
  unfold GraphShiftedContactOperatorProblem.occupationPotential
  simp only [map_add]
  exact intervalIntegral.integral_add
    (((P.realizedFeller_strong_continuous f).comp continuous_real_toNNReal).intervalIntegrable 0 T)
    (((P.realizedFeller_strong_continuous g).comp continuous_real_toNNReal).intervalIntegrable 0 T)

theorem GraphShiftedContactOperatorProblem.occupationL2_cauchy_of_potential_approx
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : ℕ → C(GraphRealization P.geometry, ℝ))
    (T : ℝ≥0) (U : ℝ → GraphRealization P.geometry → ℝ)
    (hf : ∀ n y, 0 ≤ f n y) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ n, P.occupationPotential (f n) T x ≤ B)
    (hu : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      |P.occupationPotential (f n) t y - U t y| ≤ ε) :
    CauchySeq (fun n => P.occupationL2 hκ x (f n) T) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let η := ε ^ 2 / (8 * (B + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : η * (8 * (B + 1)) = ε ^ 2 := by
    dsimp [η]
    exact div_mul_cancel₀ _ (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu η hη)
  refine ⟨N, ?_⟩
  intro n hn m hm
  have hd : ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      |P.occupationPotential (f n - f m) t y| ≤ 2 * η := by
    intro t ht y
    rw [P.occupationPotential_sub, ContinuousMap.sub_apply]
    calc
      _ = |(P.occupationPotential (f n) t y - U t y) -
          (P.occupationPotential (f m) t y - U t y)| := by congr 1; ring
      _ ≤ |P.occupationPotential (f n) t y - U t y| +
          |P.occupationPotential (f m) t y - U t y| := abs_sub _ _
      _ ≤ η + η := add_le_add (hN n hn t ht y) (hN m hm t ht y)
      _ = 2 * η := (two_mul η).symm
  have hb' : P.occupationPotential (f n + f m) T x ≤ 2 * B := by
    rw [P.occupationPotential_add, ContinuousMap.add_apply, two_mul]
    exact add_le_add (hb n) (hb m)
  have hs := P.occupation_difference_square_bound hκ x (f n) (f m) (hf n) (hf m)
    T.coe_nonneg hd
  have hs' : ‖P.occupationL2 hκ x (f n) T - P.occupationL2 hκ x (f m) T‖ ^ 2 ≤
      2 * (2 * η) * (2 * B) := by
    rw [P.occupationL2_sub_norm_sq]
    exact hs.trans (mul_le_mul_of_nonneg_left hb' (by positivity))
  rw [dist_eq_norm]
  apply (sq_lt_sq₀ (norm_nonneg _) hε.le).mp
  nlinarith

theorem GraphShiftedContactOperatorProblem.occupationL2_limit_of_potential_approx
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : ℕ → C(GraphRealization P.geometry, ℝ))
    (T : ℝ≥0) (U : ℝ → GraphRealization P.geometry → ℝ)
    (hf : ∀ n y, 0 ≤ f n y) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ n, P.occupationPotential (f n) T x ≤ B)
    (hu : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      |P.occupationPotential (f n) t y - U t y| ≤ ε) :
    ∃ L : Lp ℝ 2 (P.continuousPathLaw hκ x),
      Tendsto (fun n => P.occupationL2 hκ x (f n) T) atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete
    (P.occupationL2_cauchy_of_potential_approx hκ x f T U hf hB hb hu)

end TimeTraps.Analysis
