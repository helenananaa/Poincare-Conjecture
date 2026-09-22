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
/-- The equator is S2 by the actual tail projection. -/
theorem equator_homeomorph_sphere2 :
    ∃ e : {x : Sphere3 // (x : E4) 0 = 0} ≃ₜ Sphere2,
      ∀ x, (e x : Euclidean3) = DoubleBall.tail (x.val : E4) :=
/- SWARM_PROOF_BEGIN -/
by
  let insert0 : Euclidean3 → E4 := fun y =>
    WithLp.toLp 2 (Fin.cases 0 (fun i => y i))
  have hinsert_tail (y : Euclidean3) :
      DoubleBall.tail (insert0 y) = y := by
    ext i
    rfl
  have hinsert_head (y : Euclidean3) : insert0 y 0 = 0 := by
    rfl
  have htail_cont : Continuous (DoubleBall.tail : E4 → Euclidean3) := by
    unfold DoubleBall.tail
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    exact (PiLp.continuous_apply 2 _ i.succ)
  have hinsert_cont : Continuous insert0 := by
    dsimp [insert0]
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using (continuous_const : Continuous (fun _ : Euclidean3 => (0 : ℝ)))
    · intro j
      exact PiLp.continuous_apply 2 _ j
  have hinsert_norm (s : Sphere2) : ‖insert0 (s : Euclidean3)‖ = 1 := by
    have hs : ‖(s : Euclidean3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using s.property
    have hsq : ‖insert0 (s : Euclidean3)‖ ^ 2 = 1 := by
      rw [DoubleBall.norm_sq_split, hinsert_head, hinsert_tail]
      nlinarith [sq_nonneg ‖(s : Euclidean3)‖]
    nlinarith [norm_nonneg (insert0 (s : Euclidean3))]
  let f : {x : Sphere3 // (x : E4) 0 = 0} → Sphere2 := fun x =>
    ⟨DoubleBall.tail (x.val : E4), by
      have hx : ‖(x.val : E4)‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using x.val.property
      have hsq : ‖DoubleBall.tail (x.val : E4)‖ ^ 2 = 1 := by
        have hsplit := DoubleBall.norm_sq_split (x.val : E4)
        rw [hx, x.property] at hsplit
        nlinarith [hsplit]
      have htailnorm : ‖DoubleBall.tail (x.val : E4)‖ = 1 := by
        nlinarith [norm_nonneg (DoubleBall.tail (x.val : E4))]
      simpa only [Metric.mem_sphere, dist_zero_right] using htailnorm⟩
  let g : Sphere2 → {x : Sphere3 // (x : E4) 0 = 0} := fun s =>
    ⟨⟨insert0 (s : Euclidean3), by
        simpa only [Metric.mem_sphere, dist_zero_right] using hinsert_norm s⟩,
      hinsert_head (s : Euclidean3)⟩
  have hf : Continuous f := by
    dsimp [f]
    have hval : Continuous
        (fun x : {x : Sphere3 // (x : E4) 0 = 0} => (x.val : E4)) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (htail_cont.comp hval).subtype_mk _
  have hg : Continuous g := by
    dsimp [g]
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact hinsert_cont.comp continuous_subtype_val
  have hfg : ∀ s : Sphere2, f (g s) = s := by
    intro s
    apply Subtype.ext
    exact hinsert_tail (s : Euclidean3)
  have hgf : ∀ x : {x : Sphere3 // (x : E4) 0 = 0}, g (f x) = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [g, f, insert0, DoubleBall.tail] using x.property.symm
    · rfl
  let e : {x : Sphere3 // (x : E4) 0 = 0} ≃ₜ Sphere2 :=
    Homeomorph.mk ⟨f, g, hgf, hfg⟩ hf hg
  refine ⟨e, ?_⟩
  intro x
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
