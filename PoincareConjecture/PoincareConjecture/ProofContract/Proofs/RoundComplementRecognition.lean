import PoincareConjecture.ProofContract.Proofs.LowerHemisphereBall
import PoincareConjecture.ProofContract.Proofs.EquatorSphere
import PoincareConjecture.ProofContract.Proofs.HemisphereFrontier
import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
import PoincareConjecture.ProofContract.Proofs.DoubleBallNorm
import PoincareConjecture.ProofContract.Proofs.DoubleBallRegularity
import PoincareConjecture.ProofContract.Proofs.DoubleBallCoverage
import PoincareConjecture.ProofContract.Proofs.CoordinateBoundary
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 DoubleBall Set Function Topology
open scoped Topology Manifold ContDiff
/-- Boundary-aware complement recognition when an ACTUAL ambient homeomorphism sends the removed ball to a hemisphere. -/
theorem round_coordinate_complement_recognition {M : ClosedThreeManifold.{u}}
    (b : CoordinateBall M) (e : M ≃ₜ Sphere3)
    (he : ∀ x : M, x ∈ b.removed ↔ 0 < (e x : E4) 0) :
    ∃ (q : b.Complement ≃ₜ DoubleBall.Ball) (k : Sphere2 ≃ₜ Sphere2),
      ∀ s : Sphere2, q (b.boundary s) = DoubleBall.boundary (k s) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨ell, hell⟩ := lower_hemisphere_homeomorph_ball
  obtain ⟨u, hu⟩ := equator_homeomorph_sphere2
  have hcomp : ∀ x : M, x ∉ b.removed ↔ (e x : E4) 0 ≤ 0 := by
    intro x
    constructor
    · intro hx
      exact le_of_not_gt (fun hpos => hx ((he x).2 hpos))
    · intro hx hrem
      exact (not_lt_of_ge hx) ((he x).1 hrem)
  let r : b.Complement ≃ₜ {x : Sphere3 // (x : E4) 0 ≤ 0} := e.subtype hcomp
  let q : b.Complement ≃ₜ DoubleBall.Ball := r.trans ell
  let bd : Sphere2 → M := fun s => (b.boundary s : M)
  have hbd_range : Set.range bd = frontier b.removed := by
    rw [(coordinate_closure_frontier b).2]
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨(s : Euclidean3), ?_, rfl⟩
      simpa [Metric.mem_sphere, dist_zero_right] using s.property
    · rintro ⟨x, hx, rfl⟩
      have hnorm : ‖x‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hx
      let s : Sphere2 := ⟨x, by simpa [Metric.mem_sphere, dist_zero_right] using hnorm⟩
      refine ⟨s, ?_⟩
      rfl
  have he_removed : e '' b.removed = {y : Sphere3 | 0 < (y : E4) 0} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (he x).1 hx
    · intro hy
      refine ⟨e.symm y, (he (e.symm y)).2 ?_, ?_⟩
      · simpa using hy
      · simp
  have he_frontier : e '' frontier b.removed =
      {y : Sphere3 | (y : E4) 0 = 0} := by
    rw [e.image_frontier, he_removed, upper_hemisphere_frontier]
  have hfront_iff (x : M) : x ∈ frontier b.removed ↔
      (e x : E4) 0 = 0 := by
    constructor
    · intro hy
      have : e x ∈ e '' frontier b.removed := ⟨x, hy, rfl⟩
      rw [he_frontier] at this
      exact this
    · intro hy
      have hmem : e x ∈ e '' frontier b.removed := by
        rw [he_frontier]
        exact hy
      rcases hmem with ⟨z, hz, heq⟩
      have hzx : z = x := e.injective heq
      simpa [hzx] using hz
  let bd' : Sphere2 → {x : M // x ∈ frontier b.removed} := fun s =>
    ⟨bd s, by
      rw [← hbd_range]
      exact ⟨s, rfl⟩⟩
  have hbd_cont : Continuous bd := by
    exact continuous_subtype_val.comp
      (coordinate_boundary_isClosedEmbedding b).continuous
  have hbd_inj : Function.Injective bd := by
    intro s t hst
    have hst' : b.boundary s = b.boundary t := by
      apply Subtype.ext
      exact hst
    exact (coordinate_boundary_isClosedEmbedding b).injective hst'
  have hbd'_cont : Continuous bd' := hbd_cont.subtype_mk _
  have hbd'_bij : Function.Bijective bd' := by
    constructor
    · intro s t hst
      apply hbd_inj
      change (b.boundary s : M) = (b.boundary t : M)
      exact congrArg
        (fun z : {x : M // x ∈ frontier b.removed} => (z : M)) hst
    · intro x
      have hxrange : x.val ∈ Set.range bd := by
        rw [hbd_range]
        exact x.property
      rcases hxrange with ⟨s, hs⟩
      refine ⟨s, ?_⟩
      apply Subtype.ext
      exact hs
  let bd_homeo : Sphere2 ≃ₜ {x : M // x ∈ frontier b.removed} :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective bd' hbd'_bij) hbd'_cont
  let fr : {x : M // x ∈ frontier b.removed} ≃ₜ
      {x : Sphere3 // (x : E4) 0 = 0} := e.subtype hfront_iff
  let c : Sphere2 ≃ₜ {x : Sphere3 // (x : E4) 0 = 0} := bd_homeo.trans fr
  let k : Sphere2 ≃ₜ Sphere2 := c.trans u
  refine ⟨q, k, ?_⟩
  intro s
  apply Subtype.ext
  change (q (b.boundary s) : Euclidean3) = (k s : Euclidean3)
  change (ell (r (b.boundary s)) : Euclidean3) = (u (c s) : Euclidean3)
  rw [hell]
  have hbd_apply : ((bd_homeo s : {x : M // x ∈ frontier b.removed}) : M) =
      (b.boundary s : M) := by
    rfl
  calc
    tail ((e (b.boundary s : M)) : E4) =
        tail ((e ((bd_homeo s : {x : M // x ∈ frontier b.removed}) : M)) : E4) := by
          rw [hbd_apply]
    _ = (u (c s) : Euclidean3) := (hu (c s)).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
