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
/-- The closed lower hemisphere is the actual closed three-ball, with a prescribed map. -/
theorem lower_hemisphere_homeomorph_ball :
    ∃ e : {x : Sphere3 // (x : E4) 0 ≤ 0} ≃ₜ DoubleBall.Ball,
      ∀ x, (e x : Euclidean3) = DoubleBall.tail (x.val : E4) :=
/- SWARM_PROOF_BEGIN -/
by
  let L : Type := {x : Sphere3 // (x : E4) 0 ≤ 0}
  let f : L → Ball := fun x =>
    ⟨tail (x.val : E4), by
      have hnorm : ‖(x.val : E4)‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using x.val.property
      have hsq : ‖(tail (x.val : E4))‖ ^ 2 ≤ 1 := by
        have hsplit := norm_sq_split (x.val : E4)
        have hnormsq : ‖(x.val : E4)‖ ^ 2 = 1 := by rw [hnorm]; norm_num
        nlinarith [sq_nonneg ((x.val : E4) 0)]
      have hnonneg : 0 ≤ ‖tail (x.val : E4)‖ := norm_nonneg _
      have hle : ‖tail (x.val : E4)‖ ≤ 1 := by
        nlinarith
      simpa only [Metric.mem_closedBall, dist_zero_right] using hle⟩
  have hrad : ∀ x : L, 0 ≤ 1 - ‖tail (x.val : E4)‖ ^ 2 := by
    intro x
    have hnorm : ‖(x.val : E4)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.val.property
    have hsplit := norm_sq_split (x.val : E4)
    have hnormsq : ‖(x.val : E4)‖ ^ 2 = 1 := by rw [hnorm]; norm_num
    nlinarith [sq_nonneg ((x.val : E4) 0)]
  let g : Ball → L := fun x =>
    ⟨⟨raw false x, by
      simpa only [Metric.mem_sphere, dist_zero_right] using doubleBall_raw_norm false x⟩, by
      simp [raw]⟩
  have hfg : Function.LeftInverse g f := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change raw false (f x) = (x.val : E4)
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hsqrt : Real.sqrt (1 - ‖tail (x.val : E4)‖ ^ 2) =
          -((x.val : E4) 0) := by
        have hsq : ((x.val : E4) 0) ^ 2 =
            1 - ‖tail (x.val : E4)‖ ^ 2 := by
          have hsplit := norm_sq_split (x.val : E4)
          have hnorm : ‖(x.val : E4)‖ = 1 := by
            simpa only [Metric.mem_sphere, dist_zero_right] using x.val.property
          have hnormsq : ‖(x.val : E4)‖ ^ 2 = 1 := by rw [hnorm]; norm_num
          nlinarith
        have hnonpos : (x.val : E4) 0 ≤ 0 := x.property
        have habs : |(x.val : E4) 0| = -((x.val : E4) 0) :=
          abs_of_nonpos hnonpos
        have hsqrt : Real.sqrt (1 - ‖tail (x.val : E4)‖ ^ 2) =
            |(x.val : E4) 0| := by
          have hsqrt_nonneg := Real.sqrt_nonneg (1 - ‖tail (x.val : E4)‖ ^ 2)
          have habs_nonneg : 0 ≤ |(x.val : E4) 0| := abs_nonneg _
          have habssq : |(x.val : E4) 0| ^ 2 = ((x.val : E4) 0) ^ 2 := by
            simp
          nlinarith [Real.sq_sqrt (hrad x)]
        rw [hsqrt, habs]
      simp [f, raw, hsqrt]
    · rfl
  have hgf : Function.RightInverse g f := by
    intro x
    apply Subtype.ext
    simp only [f, g, tail_raw]
  have htail : Continuous (tail : E4 → Euclidean3) := by
    unfold tail
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    exact PiLp.continuous_apply 2 _ i.succ
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact htail.comp
      (continuous_subtype_val.comp continuous_subtype_val :
        Continuous (fun x : L => (x.val.val : E4)))
  have hraw : Continuous (raw false : Ball → E4) :=
    (doubleBall_raw_regular false).1
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact hraw
  let e₀ : L ≃ Ball :=
    { toFun := f
      invFun := g
      left_inv := hfg
      right_inv := hgf }
  refine ⟨Homeomorph.mk e₀ hf hg, ?_⟩
  intro x
  change (e₀ x : Euclidean3) = tail (x.val : E4)
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
