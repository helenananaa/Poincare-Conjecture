import PoincareConjecture.Topology.FiberSaturation.LocalDiffeomorphComparison
import PoincareConjecture.Topology.FiberSaturation.PresentedSmoothRegion
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Function Manifold
open scoped Manifold ContDiff

/-- Recover the actual parametrization of a region closure, not merely some
unspecified homeomorphism to a cylinder. All topological premises are explicit. -/
theorem presented_region_closedStrip {N : Type*} [TopologicalSpace N] [T2Space N]
    (φ : Sphere2 ≃ₜ Sphere2) {L : ℝ} (hL : 0 < L)
    (q : Sphere2 × ℝ → N) (π : N → AddCircle L)
    (hq : Continuous q) (hπ : Continuous π) (hsurj : Surjective q)
    (hbase : ∀ p : Sphere2 × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : Sphere2 => q (x, t)))
    (hglue : ∀ x t, q (x, t + L) = q (φ x, t))
    {D : Set N} (hD : IsOpen D) (hc : IsConnected D)
    (hregular : D = interior (closure D))
    (hs : FiberSaturated (q ⁻¹' frontier D)) (hne : (frontier D).Nonempty) :
    ∃ a b : ℝ, a < b ∧ b-a < L ∧
      q '' ((univ : Set Sphere2) ×ˢ Icc a b) = closure D := by
  obtain ⟨e, he⟩ := sphere_presentation_coordinates φ hL q π hq hπ hsurj hbase hfiber hglue
  have hcomp : e ∘ q = MappingTorus.proj φ.symm L := funext he
  have hs' : FiberSaturated (MappingTorus.proj φ.symm L ⁻¹' frontier (e '' D)) := by
    rw [← e.image_frontier, ← hcomp, preimage_comp, preimage_image_eq _ e.injective]
    exact hs
  have hn' : (frontier (closure (e '' D))).Nonempty := by
    rw [← e.image_closure, ← e.image_frontier,
      MappingTorus.frontier_closure_eq_of_regularOpen hD hregular]
    exact hne.image e
  obtain ⟨a, b, hab, hw, _, hcl⟩ := MappingTorus.region_short_strip φ.symm hL
    (e.isOpenMap _ hD) (hc.image _ e.continuous.continuousOn) hs' hn'
  refine ⟨a, b, hab, hw, ?_⟩
  apply e.injective.image_injective
  rw [image_image]
  change (e ∘ q) '' ((univ : Set Sphere2) ×ˢ Icc a b) = e '' closure D
  rw [hcomp, ← hcl, e.image_closure]

section SmoothClosure
variable {E F H G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace N] [T2Space N] [ChartedSpace G N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [J.Boundaryless]

/-- Smooth closed-cylinder classification for a locally diffeomorphic periodic
presentation. Unlike the earlier topological theorem, local smooth invertibility
of q is an explicit geometric premise; it is not inferred from continuity. -/
theorem sphere_region_diffeomorph_of_smoothPresentation (φ : Sphere2 ≃ₜ Sphere2)
    {L : ℝ} (hL : 0 < L) (q : Sphere2 × ℝ → N) (π : N → AddCircle L)
    (hq : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) J ∞ q)
    (hπ : Continuous π) (hsurj : Surjective q)
    (hbase : ∀ p : Sphere2 × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : Sphere2 => q (x, t)))
    (hglue : ∀ x t, q (x, t + L) = q (φ x, t))
    {D : Set N} [ChartedSpace H (closure D)] [IsManifold I ∞ (closure D)]
    (hD : IsOpen D) (hc : IsConnected D)
    (hf : IsSmoothEmbedding I J ∞ (Subtype.val : closure D → N))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hb : (Subtype.val : closure D → N) '' I.boundary (closure D) = frontier D)
    (hs : FiberSaturated (q ⁻¹' frontier D)) (hne : (frontier D).Nonempty) :
    Nonempty (↥(closure D) ≃ₘ⟮I, (𝓡 2).prod (𝓡∂ 1)⟯ (Sphere2 × Icc (0 : ℝ) 1)) := by
  have hr := regularOpen_of_smoothClosure_boundary hD hf hdim hb
  obtain ⟨a, b, hab, hw, himage⟩ := presented_region_closedStrip φ hL q π
    hq.contMDiff.continuous hπ hsurj hbase hfiber hglue hD hc hr hs hne
  letI : Fact (a < b) := ⟨hab⟩
  letI : CompactSpace Sphere2 := isCompact_iff_compactSpace.mp
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  have hstep : ∀ x t, q (φ.symm x, t+L) = q (x,t) := by
    intro x t; simpa using hglue (φ.symm x) t
  let c : ↥((univ : Set Sphere2) ×ˢ Icc a b) ≃ₜ (Sphere2 × Icc a b) :=
    (Homeomorph.Set.prod univ (Icc a b)).trans
      ((Homeomorph.Set.univ Sphere2).prodCongr (Homeomorph.refl _))
  let f : Sphere2 × Icc a b → N := fun p => q (p.1, (p.2 : ℝ))
  have hEmbed : _root_.Topology.IsEmbedding f :=
    (MappingTorus.presentation_closedStrip_embedding φ.symm hL hw q π
      hq.contMDiff.continuous hbase hfiber hstep).comp c.symm.isEmbedding
  have hRange : range f = closure D := by
    rw [← himage]
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p.1, (p.2 : ℝ)), ⟨mem_univ _, p.2.2⟩, rfl⟩
    · rintro ⟨⟨x,t⟩, ht, rfl⟩
      exact ⟨(x, ⟨t, ht.2⟩), rfl⟩
  let e : (Sphere2 × Icc a b) ≃ₜ ↥(closure D) :=
    hEmbed.toHomeomorph.trans (Homeomorph.setCongr hRange)
  let d := diffeomorphOfLocalDiffeomorphComparison
    (cylinder_inclusion_smoothEmbedding (𝓡 2) a b) hf hq e (fun _ => rfl)
  exact ⟨d.symm.trans (cylinderDiffeomorphUnit (𝓡 2) a b)⟩

end SmoothClosure
end PoincareConjecture.Topology.FiberSaturation
