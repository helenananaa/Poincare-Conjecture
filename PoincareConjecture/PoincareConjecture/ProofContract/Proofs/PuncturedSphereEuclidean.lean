import PoincareConjecture.ProofContract.Proofs.SqueezableCompactCollapse
import PoincareConjecture.ProofContract.Proofs.NestedCellSqueeze
import PoincareConjecture.ProofContract.Proofs.CollapseComplementHomeomorph
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import Mathlib.Geometry.Manifold.Instances.Sphere
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology Manifold ContDiff
/-- Stereographic coordinates on the actual punctured unit three-sphere. -/
theorem punctured_sphere3_euclidean (p : Sphere3) :
    Nonempty ({x : Sphere3 // x ≠ p} ≃ₜ Euclidean3) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
    ⟨by
      rw [finrank_euclideanSpace_fin]⟩
  let e : OpenPartialHomeomorph Sphere3 Euclidean3 := stereographic' 3 p
  have hsource : e.source = ({p}ᶜ : Set Sphere3) := by
    exact stereographic'_source p
  have htarget : e.target = (Set.univ : Set Euclidean3) := by
    exact stereographic'_target p
  let hs : {x : Sphere3 // x ≠ p} ≃ₜ e.source :=
    Homeomorph.setCongr (by
      rw [hsource]
      ext x
      change (¬ x = p) ↔ ¬ x = p
      exact Iff.rfl)
  let ht : e.target ≃ₜ Euclidean3 :=
    (Homeomorph.setCongr htarget).trans (Homeomorph.Set.univ Euclidean3)
  exact ⟨hs.trans (e.toHomeomorphSourceTarget.trans ht)⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
