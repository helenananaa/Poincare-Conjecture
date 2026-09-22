import PoincareConjecture.ProofContract.Proofs.CoordinateBoundary
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- The connected-sum quotient makes exactly the prescribed boundary identifications. -/
theorem connectedSum_quotient_fibers {A B : ClosedThreeManifold.{u}}
    (a : CoordinateBall A) (b : CoordinateBall B) (h : Sphere2 ≃ₜ Sphere2) :
    Function.Injective (fun x : a.Complement => Quot.mk (connectedSumSeam a b h) (Sum.inl x)) ∧
    Function.Injective (fun y : b.Complement => Quot.mk (connectedSumSeam a b h) (Sum.inr y)) ∧
    ∀ (x : a.Complement) (y : b.Complement),
      Quot.mk (connectedSumSeam a b h) (Sum.inl x) =
        Quot.mk (connectedSumSeam a b h) (Sum.inr y) ↔
          ∃ s : Sphere2, x = a.boundary s ∧ y = b.boundary (h s) :=
/- SWARM_PROOF_BEGIN -/
by
  have hia : Function.Injective a.boundary :=
    (coordinate_boundary_isClosedEmbedding a).injective
  have hib : Function.Injective b.boundary :=
    (coordinate_boundary_isClosedEmbedding b).injective
  let R : (a.Complement ⊕ b.Complement) →
      (a.Complement ⊕ b.Complement) → Prop :=
    fun p q =>
      p = q ∨
        (∃ s : Sphere2,
          p = Sum.inl (a.boundary s) ∧ q = Sum.inr (b.boundary (h s))) ∨
        (∃ s : Sphere2,
          p = Sum.inr (b.boundary (h s)) ∧ q = Sum.inl (a.boundary s))
  have hR : Equivalence R := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact Or.inl rfl
    · intro p q hpq
      rcases hpq with hpq | ⟨s, hp, hq⟩ | ⟨s, hp, hq⟩
      · exact Or.inl hpq.symm
      · exact Or.inr (Or.inr ⟨s, hq, hp⟩)
      · exact Or.inr (Or.inl ⟨s, hq, hp⟩)
    · intro p q r hpq hqr
      rcases hpq with hpq | ⟨s, hp, hq⟩ | ⟨s, hp, hq⟩
      · cases hpq
        exact hqr
      · rcases hqr with hqr | ⟨t, hp', hq'⟩ | ⟨t, hp', hq'⟩
        · cases hqr
          exact Or.inr (Or.inl ⟨s, hp, hq⟩)
        · cases hq.symm.trans hp'
        · have hst' : b.boundary (h s) = b.boundary (h t) :=
            Sum.inr.inj (hq.symm.trans hp')
          have hst : s = t := h.injective (hib hst')
          subst t
          exact Or.inl (hp.trans hq'.symm)
      · rcases hqr with hqr | ⟨t, hp', hq'⟩ | ⟨t, hp', hq'⟩
        · cases hqr
          exact Or.inr (Or.inr ⟨s, hp, hq⟩)
        · have hst' : a.boundary s = a.boundary t :=
            Sum.inl.inj (hq.symm.trans hp')
          have hst : s = t := hia hst'
          subst t
          exact Or.inl (hp.trans hq'.symm)
        · cases hq.symm.trans hp'
  have hseamR : ∀ p q, connectedSumSeam a b h p q → R p q := by
    intro p q hpq
    rcases hpq with ⟨s, hp, hq⟩
    exact Or.inr (Or.inl ⟨s, hp, hq⟩)
  have hgen : ∀ p q,
      Relation.EqvGen (connectedSumSeam a b h) p q ↔ R p q := by
    intro p q
    constructor
    · intro hpq
      induction hpq with
      | rel x y hxy => exact hseamR x y hxy
      | refl x => exact Or.inl rfl
      | symm x y hxy ih => exact hR.symm ih
      | trans x y z hxy hyz ihxy ihyz => exact hR.trans ihxy ihyz
    · intro hpq
      rcases hpq with hpq | ⟨s, hp, hq⟩ | ⟨s, hp, hq⟩
      · cases hpq
        exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ ⟨s, hp, hq⟩
      · exact Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ ⟨s, hq, hp⟩)
  have hquot : ∀ p q,
      Quot.mk (connectedSumSeam a b h) p = Quot.mk (connectedSumSeam a b h) q ↔
        R p q := by
    intro p q
    constructor
    · intro hpq
      exact (hgen p q).mp (Quot.eqvGen_exact hpq)
    · intro hpq
      exact Quot.eqvGen_sound ((hgen p q).mpr hpq)
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    rcases (hquot (Sum.inl x) (Sum.inl y)).mp hxy with hxy | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
    · exact Sum.inl.inj hxy
    · cases hy
    · cases hx
  · intro x y hxy
    rcases (hquot (Sum.inr x) (Sum.inr y)).mp hxy with hxy | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
    · exact Sum.inr.inj hxy
    · cases hx
    · cases hy
  · intro x y
    constructor
    · intro hxy
      rcases (hquot (Sum.inl x) (Sum.inr y)).mp hxy with hxy | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
      · cases hxy
      · exact ⟨s, Sum.inl.inj hx, Sum.inr.inj hy⟩
      · cases hx
    · rintro ⟨s, hx, hy⟩
      apply (hquot (Sum.inl x) (Sum.inr y)).mpr
      exact Or.inr (Or.inl ⟨s, congrArg Sum.inl hx, congrArg Sum.inr hy⟩)
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
