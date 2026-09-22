import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 DoubleBall Set Function Topology
open scoped Topology Manifold ContDiff
/-- The upper and lower hemisphere maps agree exactly at their common boundary. -/
theorem doubleBall_raw_cross_iff (x y : Ball) :
    raw true x = raw false y ↔ ∃ s : Sphere2, x = boundary s ∧ y = boundary s :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · intro h
    have hxy : (x : Euclidean3) = (y : Euclidean3) := by
      simpa using congrArg tail h
    have hfirst := congrArg (fun z : E4 => z 0) h
    simp [raw] at hfirst
    have hsqrt : Real.sqrt (1 - ‖(x : Euclidean3)‖ ^ 2) = 0 := by
      have hnorm : ‖(x : Euclidean3)‖ = ‖(y : Euclidean3)‖ := by
        rw [hxy]
      rw [← hnorm] at hfirst
      nlinarith [Real.sqrt_nonneg (1 - ‖(x : Euclidean3)‖ ^ 2)]
    have hxball : ‖(x : Euclidean3)‖ ≤ 1 := by
      have hxmem := x.property
      change dist (x : Euclidean3) 0 ≤ 1 at hxmem
      simpa [dist_eq_norm] using hxmem
    have hrad : 1 - ‖(x : Euclidean3)‖ ^ 2 = 0 := by
      have hnormnonneg : 0 ≤ ‖(x : Euclidean3)‖ := norm_nonneg _
      have hnonneg : 0 ≤ 1 - ‖(x : Euclidean3)‖ ^ 2 := by nlinarith
      rw [← Real.sq_sqrt hnonneg]
      rw [hsqrt]
      norm_num
    have hxnorm : ‖(x : Euclidean3)‖ = 1 := by
      nlinarith [norm_nonneg (x : Euclidean3)]
    let s : Sphere2 := ⟨(x : Euclidean3), by
      simpa only [Metric.mem_sphere, dist_zero_right] using hxnorm⟩
    exact ⟨s, Subtype.ext rfl, by apply Subtype.ext; exact hxy.symm⟩
  · rintro ⟨s, hx, hy⟩
    rw [hx, hy]
    have hs : ‖(s : Euclidean3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using s.property
    have hsB : ‖(boundary s : Euclidean3)‖ = 1 := by
      simpa [boundary] using hs
    ext i
    fin_cases i <;> simp [raw, hsB]
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
