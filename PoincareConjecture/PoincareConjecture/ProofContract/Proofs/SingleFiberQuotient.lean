import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.Proofs.ChartSupportedHomeomorph
import PoincareConjecture.ProofContract.Proofs.EuclideanBallCompression
import PoincareConjecture.ProofContract.Proofs.BufferedRadiusProfile
import PoincareConjecture.ProofContract.Proofs.RadialHomeomorphLift
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology
theorem homeomorph_of_single_fiber_quotient {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    (K : Set X) (q : X → Y) (hq : Continuous q) (hs : Surjective q)
    (hker : ∀ x y, q x = q y ↔ x=y ∨ (x ∈ K ∧ y ∈ K)) :
    ∃ e : Quot (fun x y : X => x=y ∨ (x ∈ K ∧ y ∈ K)) ≃ₜ Y,
      ∀ x, e (Quot.mk (fun x y : X => x=y ∨ (x ∈ K ∧ y ∈ K)) x) = q x :=
/- SWARM_PROOF_BEGIN -/
by
  let f : Quot (fun x y : X => x = y ∨ (x ∈ K ∧ y ∈ K)) → Y :=
    Quot.lift q (fun x y hxy => (hker x y).mpr hxy)
  have hf_cont : Continuous f := by
    dsimp [f]
    exact continuous_quot_lift (fun x y hxy => (hker x y).mpr hxy) hq
  have hf_inj : Function.Injective f := by
    intro a
    refine Quot.inductionOn a ?_
    intro x b
    refine Quot.inductionOn b ?_
    intro y hxy
    apply Quot.sound
    apply (hker x y).mp
    simpa [f] using hxy
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨Quot.mk _ x, by simp [f]⟩
  let e : Quot (fun x y : X => x = y ∨ (x ∈ K ∧ y ∈ K)) ≃ Y :=
    Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := e) ?_, ?_⟩
  · exact hf_cont
  · intro x
    change e (Quot.mk _ x) = q x
    simp [e, f]
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
