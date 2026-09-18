import PoincareConjecture

open Set Bundle
open PoincareConjecture.Topology.FiberSaturation
open CircleBundle

abbrev SphereExampleBundle := Bundle.Trivial (AddCircle (1 : ℝ)) Sphere2

local instance : T2Space (TotalSpace Sphere2 SphereExampleBundle) :=
  (Bundle.Trivial.homeomorphProd (AddCircle (1 : ℝ)) Sphere2).symm.t2Space

-- A genuine standard FiberBundle, with no supplied period map or twist.
example : ∃ φ : Sphere2 ≃ₜ Sphere2,
    ∃ e : ClosedMappingTorus φ 1 ≃ₜ TotalSpace Sphere2 SphereExampleBundle,
      ∀ p : Sphere2 × Icc (0 : ℝ) 1,
        (e (Quot.mk _ p)).proj = ((p.2 : ℝ) : AddCircle (1 : ℝ)) :=
  abstract_sphere_bundle_closed_mappingTorus SphereExampleBundle (by norm_num)

-- Full surjectivity is tested on the bundle-derived parametrization.
example : Function.Surjective (cutMap Sphere2 SphereExampleBundle) :=
  surjective_cutMap Sphere2 SphereExampleBundle (by norm_num)

-- The returned twist really glues the two distinct cylinder ends.
example (x : Sphere2) :
    cutMap Sphere2 SphereExampleBundle (x, ⟨1,by norm_num,le_rfl⟩) =
      cutMap Sphere2 SphereExampleBundle
        (monodromy Sphere2 SphereExampleBundle (by norm_num) x, ⟨0,le_rfl,by norm_num⟩) :=
  cutMap_endpoints Sphere2 SphereExampleBundle (by norm_num) x

-- Interior points cannot be spuriously identified, even in the same fiber.
example (x y : Sphere2) (hne : x ≠ y) :
    cutMap Sphere2 SphereExampleBundle (x, ⟨1/2,by norm_num,by norm_num⟩) ≠
      cutMap Sphere2 SphereExampleBundle (y, ⟨1/2,by norm_num,by norm_num⟩) := by
  intro h
  exact hne (cutMap_fiber_injective Sphere2 SphereExampleBundle _ h)

-- The seam relation is explicitly checked, not defined to be a map's kernel.
example (x : Sphere2) :
    ¬ Seam (Homeomorph.refl Sphere2)
      (x, (⟨0,by norm_num,by norm_num⟩ : Icc (0 : ℝ) 1))
      (x, (⟨1/2,by norm_num,by norm_num⟩ : Icc (0 : ℝ) 1)) := by
  norm_num [Seam, Prod.ext_iff, Subtype.ext_iff]

-- The generic theorem also handles a compact discrete fiber.
abbrev DiscreteExampleBundle := Bundle.Trivial (AddCircle (2 : ℝ)) (Fin 2)

local instance : T2Space (TotalSpace (Fin 2) DiscreteExampleBundle) :=
  (Bundle.Trivial.homeomorphProd (AddCircle (2 : ℝ)) (Fin 2)).symm.t2Space

example : ∃ φ : Fin 2 ≃ₜ Fin 2,
    ∃ e : ClosedMappingTorus φ 2 ≃ₜ TotalSpace (Fin 2) DiscreteExampleBundle,
      ∀ p : Fin 2 × Icc (0 : ℝ) 2,
        (e (Quot.mk _ p)).proj = ((p.2 : ℝ) : AddCircle (2 : ℝ)) :=
  abstract_bundle_closed_mappingTorus (Fin 2) DiscreteExampleBundle (by norm_num)
