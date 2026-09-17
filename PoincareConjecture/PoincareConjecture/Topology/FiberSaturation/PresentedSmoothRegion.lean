import PoincareConjecture.Topology.FiberSaturation.PresentationOpenness

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Function Manifold
open scoped Manifold ContDiff

/-- Construct global quotient coordinates from a continuous sphere presentation.
The source convention q(x,t+L)=q(φ x,t) is matched with the inverse deck twist.
Neither a global homeomorphism nor quotient openness is assumed. -/
theorem sphere_presentation_coordinates {N : Type*} [TopologicalSpace N] [T2Space N]
    (φ : Sphere2 ≃ₜ Sphere2) {L : ℝ} (hL : 0 < L)
    (q : Sphere2 × ℝ → N) (π : N → AddCircle L)
    (hq : Continuous q) (hπ : Continuous π) (hsurj : Surjective q)
    (hbase : ∀ p : Sphere2 × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : Sphere2 => q (x, t)))
    (hglue : ∀ x t, q (x, t + L) = q (φ x, t)) :
    ∃ e : N ≃ₜ MappingTorus.Space φ.symm L, ∀ p, e (q p) = MappingTorus.proj φ.symm L p := by
  letI : CompactSpace Sphere2 := isCompact_iff_compactSpace.mp
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  have hstep : ∀ x t, q (φ.symm x, t + L) = q (x, t) := by
    intro x t
    simpa using hglue (φ.symm x) t
  have hquot := MappingTorus.presentation_isOpenQuotientMap φ.symm hL q π hq hπ hsurj hbase hfiber hstep
  let e := MappingTorus.presentationHomeomorph φ.symm L q π hbase hfiber hstep hquot
  refine ⟨e.symm, fun p => ?_⟩
  apply e.injective
  rw [e.apply_symm_apply]
  rfl

section SmoothRegion
variable {E F H G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace N] [T2Space N] [ChartedSpace G N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [J.Boundaryless]

/-- The smooth-closure region theorem now starts with a continuous bundle
presentation q rather than a preexisting quotient-coordinate homeomorphism.
All smooth structures and boundary conditions remain those on the original N. -/
theorem sphere_region_of_presented_smoothClosure (φ : Sphere2 ≃ₜ Sphere2)
    {L : ℝ} (hL : 0 < L) (q : Sphere2 × ℝ → N) (π : N → AddCircle L)
    (hq : Continuous q) (hπ : Continuous π) (hsurj : Surjective q)
    (hbase : ∀ p : Sphere2 × ℝ, π (q p) = (p.2 : AddCircle L))
    (hfiber : ∀ t : ℝ, Injective (fun x : Sphere2 => q (x, t)))
    (hglue : ∀ x t, q (x, t + L) = q (φ x, t))
    {D : Set N} [ChartedSpace H (closure D)] [IsManifold I ∞ (closure D)]
    (hD : IsOpen D) (hc : IsConnected D)
    (hf : IsSmoothEmbedding I J ∞ (Subtype.val : closure D → N))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hb : (Subtype.val : closure D → N) '' I.boundary (closure D) = frontier D)
    (hs : FiberSaturated (q ⁻¹' frontier D)) (hne : (frontier D).Nonempty) :
    Nonempty (↥(closure D) ≃ₜ (Sphere2 × Icc (0 : ℝ) 1)) := by
  obtain ⟨e, he⟩ := sphere_presentation_coordinates φ hL q π hq hπ hsurj hbase hfiber hglue
  have hinv (p : Sphere2 × ℝ) : e.symm (MappingTorus.proj φ.symm L p) = q p := by
    rw [← he p, e.symm_apply_apply]
  have hpull : MappingTorus.proj φ.symm L ⁻¹' (e '' frontier D) = q ⁻¹' frontier D := by
    simpa only [Homeomorph.symm_symm] using
      MappingTorus.presentation_preimage_inverse_image φ.symm L q e.symm hinv (frontier D)
  apply sphere_region_of_smoothClosure φ hL e hD hc hf hdim hb ?_ hne
  rwa [hpull]

end SmoothRegion
end PoincareConjecture.Topology.FiberSaturation
