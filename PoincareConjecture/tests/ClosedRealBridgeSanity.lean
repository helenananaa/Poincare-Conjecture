import PoincareConjecture

open Set Bundle Function
open PoincareConjecture.Topology.FiberSaturation
open CircleBundle

-- Hausdorffness does not require a compact fiber.
example : T2Space (MappingTorus.Space (Homeomorph.addRight (1 : ℝ)) 2) :=
  MappingTorus.space_t2Space _ (by norm_num)

-- A non-involutive twist detects the inverse-sign convention at the seam.
example : fundamentalProjection (Homeomorph.addRight (1 : ℝ)) 2
    (0,⟨2,by norm_num,le_rfl⟩) =
    fundamentalProjection (Homeomorph.addRight (1 : ℝ)) 2
      (1,⟨0,le_rfl,by norm_num⟩) := by
  simpa using fundamentalProjection_endpoints (Homeomorph.addRight (1 : ℝ))
    (by norm_num : (0 : ℝ) < 2) 0

-- Reversing that seam direction is genuinely wrong for this twist.
example : fundamentalProjection (Homeomorph.addRight (1 : ℝ)) 2
    (0,⟨2,by norm_num,le_rfl⟩) ≠
    fundamentalProjection (Homeomorph.addRight (1 : ℝ)) 2
      (-1,⟨0,le_rfl,by norm_num⟩) := by
  intro h
  have hs := (fundamentalProjection_eq_iff_seam _ (by norm_num) _ _).mp h
  norm_num [Seam, Prod.ext_iff, Subtype.ext_iff] at hs

-- Positive period is essential for injectivity on a fixed real-height fiber.
example : MappingTorus.proj (Homeomorph.addRight (1 : ℝ)) 0 (0,7) =
    MappingTorus.proj (Homeomorph.addRight (1 : ℝ)) 0 (1,7) := by
  apply (MappingTorus.proj_eq_iff _ _ _ _).mpr
  exact ⟨1,by norm_num [MappingTorus.deck]⟩

abbrev BridgeSphereBundle := Bundle.Trivial (AddCircle (2 : ℝ)) Sphere2
local instance : T2Space (TotalSpace Sphere2 BridgeSphereBundle) :=
  (Bundle.Trivial.homeomorphProd (AddCircle (2 : ℝ)) Sphere2).symm.t2Space
local instance : CompactSpace Sphere2 := isCompact_iff_compactSpace.mp
  (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

-- Standard FiberBundle data alone produce an all-real-axis presentation.
example : ∃ φ : Sphere2 ≃ₜ Sphere2, ∃ q : Sphere2 × ℝ → TotalSpace Sphere2 BridgeSphereBundle,
    Continuous q ∧ Surjective q ∧ (∀ p, (q p).proj = (p.2 : AddCircle (2 : ℝ))) ∧
    (∀ t, Injective (fun x : Sphere2 => q (x,t))) ∧
    (∀ x t, q (x,t+2) = q (φ x,t)) ∧ IsLocalHomeomorph q :=
  abstract_sphere_bundle_real_presentation BridgeSphereBundle (by norm_num)

-- The map agrees with the earlier cut at the upper seam, not just inside it.
example (x : Sphere2) : realPresentation Sphere2 BridgeSphereBundle (by norm_num) (x,2) =
    cutMap Sphere2 BridgeSphereBundle (x,⟨2,by norm_num,le_rfl⟩) :=
  realPresentation_cut Sphere2 BridgeSphereBundle (by norm_num) (x,⟨2,by norm_num⟩)

example (φ : Sphere2 ≃ₜ Sphere2) (p : Sphere2 × Icc (0 : ℝ) 2) :
    closedRealHomeomorph φ (by norm_num) (Quot.mk _ p) =
      MappingTorus.proj φ.symm 2 (p.1,(p.2 : ℝ)) := rfl

-- Boundary membership is expressed using the genuine bundle projection.
example (A : Set (AddCircle (2 : ℝ))) :
    ProjectionSaturated (TotalSpace.proj (F := Sphere2) (E := BridgeSphereBundle))
      (TotalSpace.proj ⁻¹' A) := by
  intro z w he hz
  change w.proj ∈ A
  rwa [← he]

-- Integration contract: no q, cut, or chosen twist appears among the inputs.
example {D : Set (TotalSpace Sphere2 BridgeSphereBundle)}
    (ho : IsOpen D) (hc : IsConnected D) (hr : D = interior (closure D))
    (hs : ProjectionSaturated (TotalSpace.proj (F := Sphere2) (E := BridgeSphereBundle))
      (frontier D)) (hn : (frontier D).Nonempty) :
    Nonempty (↥(closure D) ≃ₜ (Sphere2 × Icc (0 : ℝ) 1)) :=
  abstract_sphere_bundle_regular_region BridgeSphereBundle (by norm_num) ho hc hr hs hn
