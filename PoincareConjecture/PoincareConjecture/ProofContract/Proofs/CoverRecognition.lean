import PoincareConjecture.ProofContract.V1.Obligations

/-! A concrete solution of one frozen leaf, proved by unique covering lifts. -/

universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1

/-- A connected covering of a simply connected manifold is trivial.
This proves the existing contract; it does not change its hypotheses. -/
theorem sphere_cover_recognition : SphereCoverRecognitionStatement.{u} := by
  intro M hsc hcover
  letI : SimplyConnectedSpace M := hsc
  obtain ⟨p, hp, _hsurj⟩ := hcover
  let e₀ : Sphere3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨g, ⟨hg₀, hpg⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id M) (p e₀) e₀ rfl
  have hright : ∀ x, p (g x) = x := fun x => congrFun hpg x
  have hleftFun : (fun x => g (p x)) = id := by
    apply hp.eq_of_comp_eq (g.continuous.comp hp.continuous) continuous_id
      (by funext x; exact hright (p x)) e₀ hg₀
  have hleft : ∀ x, g (p x) = x := fun x => congrFun hleftFun x
  exact ⟨(show Sphere3 ≃ₜ M from
    { toEquiv := { toFun := p, invFun := g, left_inv := hleft, right_inv := hright }
      continuous_toFun := hp.continuous
      continuous_invFun := g.continuous }).symm⟩

end PoincareConjecture.ProofContract.Proofs
