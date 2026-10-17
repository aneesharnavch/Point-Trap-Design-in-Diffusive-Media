module

public import TimeTraps.Probability.ReflectedFellerIntegral

@[expose] public section

/-! Uniform limits of the actual semigroup variation identities preserve
the generator action. The finite-cosine specialization assumes only
convergence of the functions and their explicitly computed generator
values, deriving every variation identity from the checked finite core. -/

namespace TimeTraps.Probability

open Set Filter TimeTraps.Analysis
open scoped Topology

theorem reflectedFeller_integral_closed (L : ℝ) (hL : 0 < L) (D : ℝ)
    (u v : ℕ → C(Icc (0 : ℝ) L, ℝ)) (f g : C(Icc (0 : ℝ) L, ℝ))
    (hu : Tendsto u atTop (𝓝 f)) (hv : Tendsto v atTop (𝓝 g))
    (h : ∀ n t, 0 ≤ t → reflectedFellerTimeOperator L hL D t (u n) - u n =
      reflectedFellerIntegralOperator L hL D t (v n)) :
    ∀ t, 0 ≤ t → reflectedFellerTimeOperator L hL D t f - f =
      reflectedFellerIntegralOperator L hL D t g := by
  intro t ht
  have hleft := (((reflectedFellerTimeOperator L hL D t).continuous.tendsto f).comp hu).sub hu
  have hright := ((reflectedFellerIntegralOperator L hL D t).continuous.tendsto g).comp hv
  have he : (fun n => reflectedFellerTimeOperator L hL D t (u n) - u n) =
      (fun n => reflectedFellerIntegralOperator L hL D t (v n)) :=
    funext (fun n => h n t ht)
  simp only [Function.comp_apply] at hleft
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

theorem reflectedFeller_generator_of_approximation (L : ℝ) (hL : 0 < L) (D : ℝ)
    (u v : ℕ → C(Icc (0 : ℝ) L, ℝ)) (f g : C(Icc (0 : ℝ) L, ℝ))
    (hu : Tendsto u atTop (𝓝 f)) (hv : Tendsto v atTop (𝓝 g))
    (h : ∀ n t, 0 ≤ t → reflectedFellerTimeOperator L hL D t (u n) - u n =
      reflectedFellerIntegralOperator L hL D t (v n)) :
    HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t f) g (Ici 0) 0 :=
  reflectedFeller_generator_of_integral L hL D f g
    (reflectedFeller_integral_closed L hL D u v f g hu hv h)

theorem reflectedFeller_generator_of_cosine_graph_limit (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
    (f g : C(Icc (0 : ℝ) L, ℝ))
    (hf : Tendsto (fun k => ∑ n ∈ s k, c k n • neumannCosine L n) atTop (𝓝 f))
    (hg : Tendsto (fun k => ∑ n ∈ s k,
      (c k n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)) • neumannCosine L n) atTop (𝓝 g)) :
    HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t f) g (Ici 0) 0 := by
  apply reflectedFeller_generator_of_approximation L hL D _ _ f g hf hg
  intro k t ht
  exact reflectedFeller_finite_cosine_integral L hL D hD (s k) (c k) t ht

end TimeTraps.Probability
