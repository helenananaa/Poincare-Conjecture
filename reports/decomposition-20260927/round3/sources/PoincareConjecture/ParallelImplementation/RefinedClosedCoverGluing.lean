import PoincareConjecture.ProofContract.Refinement20260927.ClosedCut
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedClosedCoverGluing
open PoincareConjecture.ProofContract.Refinement20260927
theorem closed_cover_gluing : ClosedCoverGluingStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro M U V hU hV hcover bU bV hboundary hinter
  let R := rawSeam bU bV
    (Homeomorph.refl PoincareConjecture.ProofContract.V1.Sphere2)
  let f : U ⊕ V → M := Sum.elim Subtype.val Subtype.val
  have hf : ∀ x y, R x y → f x = f y := by
    intro x y hxy
    change rawSeam bU bV
      (Homeomorph.refl PoincareConjecture.ProofContract.V1.Sphere2) x y at hxy
    rcases hxy with ⟨s, rfl, rfl⟩
    simpa [f] using hboundary s
  let F : Quot R → M := Quot.lift f hf
  have hF_surj : Function.Surjective F := by
    intro x
    have hx : x ∈ U ∪ V := by rw [hcover]; simp
    rcases hx with hxu | hxv
    · refine ⟨Quot.mk R (Sum.inl ⟨x, hxu⟩), ?_⟩
      rfl
    · refine ⟨Quot.mk R (Sum.inr ⟨x, hxv⟩), ?_⟩
      rfl
  have hF_inj : Function.Injective F := by
    intro q r hqr
    induction q using Quot.ind with
    | _ x =>
      induction r using Quot.ind with
      | _ y =>
        change f x = f y at hqr
        cases x with
        | inl x =>
          cases y with
          | inl y =>
            change (x : M) = y at hqr
            have hxy : x = y := Subtype.ext hqr
            subst y
            rfl
          | inr y =>
            change (x : M) = (y : M) at hqr
            have hmem : (x : M) ∈ U ∩ V :=
              ⟨x.property, hqr ▸ y.property⟩
            obtain ⟨s, hs⟩ := (hinter x).mp hmem
            have hx : bU s = x := Subtype.ext hs
            have hy : bV s = y := Subtype.ext ((hboundary s).symm.trans (hs.trans hqr))
            apply Quot.sound
            exact ⟨s, congrArg Sum.inl hx.symm, congrArg Sum.inr hy.symm⟩
        | inr x =>
          cases y with
          | inl y =>
            change (x : M) = (y : M) at hqr
            have hmem : (y : M) ∈ U ∩ V :=
              ⟨y.property, hqr.symm ▸ x.property⟩
            obtain ⟨s, hs⟩ := (hinter y).mp hmem
            have hy : bU s = y := Subtype.ext hs
            have hx : bV s = x := Subtype.ext ((hboundary s).symm.trans (hs.trans hqr.symm))
            apply Eq.symm
            apply Quot.sound
            exact ⟨s, congrArg Sum.inl hy.symm, congrArg Sum.inr hx.symm⟩
          | inr y =>
            change (x : M) = y at hqr
            have hxy : x = y := Subtype.ext hqr
            subst y
            rfl
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  letI : CompactSpace (U ⊕ V) := inferInstance
  have hF_cont : Continuous F := by
    apply continuous_quot_lift hf
    exact Continuous.sumElim continuous_subtype_val continuous_subtype_val
  let eEquiv : Quot R ≃ M := Equiv.ofBijective F ⟨hF_inj, hF_surj⟩
  have hequiv_cont : Continuous eEquiv := by
    change Continuous F
    exact hF_cont
  let e : Quot R ≃ₜ M := Continuous.homeoOfEquivCompactToT2 hequiv_cont
  exact ⟨e.symm⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedClosedCoverGluing
