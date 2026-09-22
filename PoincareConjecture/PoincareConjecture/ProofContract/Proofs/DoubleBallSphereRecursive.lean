import PoincareConjecture.ProofContract.Proofs.DoubleBallNorm
import PoincareConjecture.ProofContract.Proofs.DoubleBallRegularity
import PoincareConjecture.ProofContract.Proofs.DoubleBallCoverage
import PoincareConjecture.ProofContract.Proofs.DoubleBallIntersection
import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 DoubleBall Set Function Topology
open scoped Topology Manifold ContDiff
/-- Two actual closed balls glued along their entire boundary form the three-sphere. -/
theorem doubleBall_identity_sphere_recursive :
    Nonempty (Space (Homeomorph.refl Sphere2) ≃ₜ Sphere3) :=
/- SWARM_PROOF_BEGIN -/
by
  let sphereRaw : Bool → Ball → Sphere3 := fun upper x =>
    ⟨raw upper x, by
      simpa only [Metric.mem_sphere, dist_zero_right] using doubleBall_raw_norm upper x⟩
  have hsphereRaw (upper : Bool) : Continuous (sphereRaw upper) := by
    dsimp [sphereRaw]
    exact (doubleBall_raw_regular upper).1.subtype_mk (fun x => by
      simpa only [Metric.mem_sphere, dist_zero_right] using doubleBall_raw_norm upper x)
  have hrel : ∀ p q, seam (Homeomorph.refl Sphere2) p q →
      Sum.elim (sphereRaw true) (sphereRaw false) p =
        Sum.elim (sphereRaw true) (sphereRaw false) q := by
    intro p q hpq
    rcases hpq with ⟨s, rfl, rfl⟩
    apply Subtype.ext
    simpa [sphereRaw] using
      (doubleBall_raw_cross_iff (boundary s) (boundary s)).2 ⟨s, rfl, rfl⟩
  let Ffun : Space (Homeomorph.refl Sphere2) → Sphere3 :=
    Quot.lift (Sum.elim (sphereRaw true) (sphereRaw false)) hrel
  have hFcont : Continuous Ffun := by
    exact continuous_quot_lift hrel
      ((hsphereRaw true).sumElim (hsphereRaw false))
  have hFsurj : Function.Surjective Ffun := by
    intro p
    rcases doubleBall_raw_covers p with ⟨upper, x, hx⟩
    cases upper with
    | false =>
        refine ⟨Quot.mk (seam (Homeomorph.refl Sphere2)) (Sum.inr x), ?_⟩
        apply Subtype.ext
        simpa [Ffun, sphereRaw] using hx
    | true =>
        refine ⟨Quot.mk (seam (Homeomorph.refl Sphere2)) (Sum.inl x), ?_⟩
        apply Subtype.ext
        simpa [Ffun, sphereRaw] using hx
  have hmk : ∀ p q : Ball ⊕ Ball,
      Ffun (Quot.mk (seam (Homeomorph.refl Sphere2)) p) =
        Ffun (Quot.mk (seam (Homeomorph.refl Sphere2)) q) →
      Quot.mk (seam (Homeomorph.refl Sphere2)) p =
        Quot.mk (seam (Homeomorph.refl Sphere2)) q := by
    intro p q hpq
    cases p with
    | inl x =>
        cases q with
        | inl y =>
            have hxy : raw true x = raw true y := by
              simpa [Ffun, sphereRaw] using
                congrArg (fun z : Sphere3 => (z : E4)) hpq
            have hxy' : x = y := (doubleBall_raw_regular true).2 hxy
            subst y
            rfl
        | inr y =>
            have hxy : raw true x = raw false y := by
              simpa [Ffun, sphereRaw] using
                congrArg (fun z : Sphere3 => (z : E4)) hpq
            obtain ⟨s, hx, hy⟩ := (doubleBall_raw_cross_iff x y).1 hxy
            exact Quot.sound ⟨s, congrArg Sum.inl hx, congrArg Sum.inr hy⟩
    | inr x =>
        cases q with
        | inl y =>
            have hxy : raw true y = raw false x := by
              simpa [Ffun, sphereRaw] using
                congrArg (fun z : Sphere3 => (z : E4)) hpq.symm
            obtain ⟨s, hy, hx⟩ := (doubleBall_raw_cross_iff y x).1 hxy
            exact (Quot.sound ⟨s, congrArg Sum.inl hy, congrArg Sum.inr hx⟩).symm
        | inr y =>
            have hxy : raw false x = raw false y := by
              simpa [Ffun, sphereRaw] using
                congrArg (fun z : Sphere3 => (z : E4)) hpq
            have hxy' : x = y := (doubleBall_raw_regular false).2 hxy
            subst y
            rfl
  have hFinj : Function.Injective Ffun := by
    intro z w hzw
    obtain ⟨p, rfl⟩ := Quot.exists_rep z
    obtain ⟨q, rfl⟩ := Quot.exists_rep w
    exact hmk p q hzw
  have hFhome : IsHomeomorph Ffun :=
    (isHomeomorph_iff_continuous_bijective).2 ⟨hFcont, ⟨hFinj, hFsurj⟩⟩
  exact ⟨hFhome.homeomorph Ffun⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
