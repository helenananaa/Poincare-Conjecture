import PoincareConjecture.ProofContract.Proofs.SqueezableCompactCollapse
import PoincareConjecture.ProofContract.Proofs.SingleFiberQuotient
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology
/-- Equal collapse fibers identify the two targets, preserving any fixed marked subset. -/
theorem recognition_from_equal_collapse_fibers {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    (K S : Set X) (f : X → Y) (g : X → X)
    (hf : Continuous f) (hfs : Surjective f) (hg : Continuous g) (hgs : Surjective g)
    (hfk : ∀ x y, f x=f y ↔ x=y ∨ (x∈K ∧ y∈K))
    (hgk : ∀ x y, g x=g y ↔ x=y ∨ (x∈K ∧ y∈K))
    (hfix : ∀ x∈S, g x=x) :
    ∃ e : X ≃ₜ Y, (∀ x, e (g x)=f x) ∧ (∀ x∈S, e x=f x) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨ef, hef⟩ := homeomorph_of_single_fiber_quotient K f hf hfs hfk
  obtain ⟨eg, heg⟩ := homeomorph_of_single_fiber_quotient K g hg hgs hgk
  let e : X ≃ₜ Y := eg.symm.trans ef
  have heq : ∀ x, e (g x) = f x := by
    intro x
    have hquot : eg.symm (g x) = Quot.mk
        (fun x y : X => x = y ∨ (x ∈ K ∧ y ∈ K)) x := by
      apply eg.injective
      rw [eg.apply_symm_apply]
      exact (heg x).symm
    simp [e, hquot, hef x]
  refine ⟨e, heq, ?_⟩
  intro x hx
  calc
    e x = e (g x) := congrArg e (hfix x hx).symm
    _ = f x := heq x
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
