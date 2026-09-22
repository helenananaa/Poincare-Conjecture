import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- A pi1-surjective map through a simply connected space has trivial target pi1. -/
theorem pi1_trivial_from_surjective_factorization
    {C X Y : Type*} [TopologicalSpace C] [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] (j : C(C, X)) (r : C(X, Y)) (g : C(C, Y))
    (hcomp : r.comp j = g) (c : C)
    (hsurj : Surjective (FundamentalGroup.map g c)) :
    Subsingleton (FundamentalGroup Y (g c)) :=
/- SWARM_PROOF_BEGIN -/
by
  rw [← hcomp] at hsurj ⊢
  constructor
  intro a b
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  have hab : FundamentalGroup.map j c a' = FundamentalGroup.map j c b' :=
    Subsingleton.elim _ _
  have hab' := congrArg (fun z => FundamentalGroup.map r (j c) z) hab
  have hmap (d : FundamentalGroup C c) :
      FundamentalGroup.map r (j c) (FundamentalGroup.map j c d) =
        FundamentalGroup.map (r.comp j) c d := by
    change ((FundamentalGroup.toPath d).map j).map r = _
    rw [← Path.Homotopic.Quotient.map_comp]
    rfl
  exact (hmap a').symm.trans <| hab'.trans (hmap b')
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
