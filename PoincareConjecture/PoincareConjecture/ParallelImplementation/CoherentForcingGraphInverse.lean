import PoincareConjecture.ParallelImplementation.ForcingGraphNearIdentityInverse
import PoincareConjecture.ParallelImplementation.ForcingGraphInverseLipschitz
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoherentForcingGraphInverse
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
theorem exists_coherent_forcing_graph_inverse
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [CompleteSpace A]
    (T alpha q R : ℝ) (hq0 : 0 ≤ q) (hq : q < 1) (hR : 0 ≤ R) :
    let S := {a : ForcingJet A T // a ∈ forcingGraph A T alpha ∧ ‖a.1‖ ≤ q ∧ ‖a.2‖ ≤ R}
    ∃ I : S → ForcingJet A T,
      (∀ a, I a ∈ forcingGraph A T alpha ∧
        (∀ p : Slab T, (1-a.1.1 p)*(I a).1 p=1 ∧ (I a).1 p*(1-a.1.1 p)=1) ∧
        ‖I a‖ ≤ max (1/(1-q)) ((1/(1-q))^2*R)) ∧
      (∀ a c, ‖I a-I c‖ ≤
        ((1/(1-q))^2+2*(1/(1-q))^3*R)*‖a.1-c.1‖) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let S := {a : ForcingJet A T // a ∈ forcingGraph A T alpha ∧
    ‖a.1‖ ≤ q ∧ ‖a.2‖ ≤ R}
  let M : ℝ := 1 / (1 - q)
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hchoice (a : S) :
      ∃ b : ForcingJet A T, b ∈ forcingGraph A T alpha ∧
        (∀ p : Slab T, (1-a.1.1 p)*b.1 p = 1 ∧
          b.1 p*(1-a.1.1 p)=1) ∧
        (∀ p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T,
          b.2 p = b.1 p.1.1*a.1.2 p*b.1 p.1.2) ∧
        ‖b.1‖ ≤ M ∧ ‖b.2‖ ≤ M^2*‖a.1.2‖ ∧
        ‖b‖ ≤ max M (M^2*‖a.1.2‖) := by
    obtain ⟨b, hgraph, hid, hinc, hb, hderiv, hnorm⟩ :=
      PoincareConjecture.ParallelImplementation.ForcingGraphNearIdentityInverse.exists_forcing_graph_near_identity_inverse
        T alpha q hq0 hq a.1 a.2.1 a.2.2.1
    refine ⟨b, hgraph, hid, hinc, ?_, hderiv, ?_⟩
    · simpa [M] using hb
    · simpa [M] using hnorm
  let chosen : S → ForcingJet A T := fun a => Classical.choose (hchoice a)
  have chosen_spec (a : S) := Classical.choose_spec (hchoice a)
  refine ⟨chosen, ?_, ?_⟩
  · intro a
    obtain ⟨hgraph, hid, hinc, hb, hderiv, hnorm⟩ := chosen_spec a
    refine ⟨hgraph, hid, ?_⟩
    calc
      ‖chosen a‖ ≤ max M (M^2*‖a.1.2‖) := hnorm
      _ ≤ max M (M^2*R) := max_le_max le_rfl
        (mul_le_mul_of_nonneg_left a.2.2.2 (sq_nonneg M))
  · intro a c
    obtain ⟨_, hia, hiaInc, hiaN, _, _⟩ := chosen_spec a
    obtain ⟨_, hic, hicInc, hicN, _, _⟩ := chosen_spec c
    exact PoincareConjecture.ParallelImplementation.ForcingGraphInverseLipschitz.forcing_graph_inverse_lipschitz
      T a.1 c.1 (chosen a) (chosen c) M R
      hM hR
      (fun p => (hia p).2)
      (fun p => (hic p).1)
      hiaInc hicInc
      hiaN hicN a.2.2.2 c.2.2.2
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoherentForcingGraphInverse
