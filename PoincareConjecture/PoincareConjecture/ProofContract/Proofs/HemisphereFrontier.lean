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
/-- The boundary of the genuine open upper hemisphere is exactly its equator. -/
theorem upper_hemisphere_frontier :
    frontier {x : Sphere3 | 0 < (x : E4) 0} = {x : Sphere3 | (x : E4) 0 = 0} :=
/- SWARM_PROOF_BEGIN -/
by
  let A : Set Sphere3 := {x : Sphere3 | 0 < (x : E4) 0}
  let C : Set Sphere3 := {x : Sphere3 | 0 ≤ (x : E4) 0}
  have hcoord : Continuous (fun x : Sphere3 => (x : E4) 0) := by
    fun_prop
  have hopen : IsOpen A := by
    exact isOpen_lt continuous_const hcoord
  have hclosed : IsClosed C := by
    exact isClosed_le continuous_const hcoord
  have hequator : ∀ x : Sphere3, (x : E4) 0 = 0 → x ∈ closure A := by
    intro x hx0
    have hxnorm : ‖(x : E4)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have hxtailnorm : ‖tail (x : E4)‖ = 1 := by
      have hsplit := norm_sq_split (x : E4)
      rw [hx0] at hsplit
      nlinarith [norm_nonneg (tail (x : E4))]
    let v : ℝ → E4 := fun s => WithLp.toLp 2 (Fin.cases s
      (fun i => (tail (x : E4)) i))
    have hv : Continuous v := by
      dsimp [v]
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      refine Fin.cases ?_ ?_ i
      · exact continuous_id
      · intro i
        exact continuous_const
    have htailv (s : ℝ) : tail (v s) = tail (x : E4) := by
      ext i
      rfl
    have hv_ne (s : ℝ) : v s ≠ 0 := by
      intro hs
      have : tail (x : E4) = 0 := by
        rw [← htailv s, hs]
        rfl
      rw [this] at hxtailnorm
      norm_num at hxtailnorm
    let q : ℝ → E4 := fun s => (‖v s‖)⁻¹ • v s
    have hq : Continuous q := by
      dsimp [q]
      exact ((continuous_norm.comp hv).inv₀ (fun s => norm_ne_zero_iff.mpr (hv_ne s))).smul hv
    have hv_zero : v 0 = (x : E4) := by
      ext i
      refine Fin.cases ?_ ?_ i
      · simp [v, hx0]
      · intro i
        rfl
    have hq_zero : q 0 = (x : E4) := by
      dsimp [q]
      rw [hv_zero, hxnorm]
      simp
    have hqnorm (s : ℝ) : ‖q s‖ = 1 := by
      have hs : 0 < ‖v s‖ := norm_pos_iff.mpr (hv_ne s)
      simp only [q, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs,
        inv_mul_cancel₀ hs.ne']
    have hqcoord (s : ℝ) : (q s) 0 = s / ‖v s‖ := by
      simp [q, v, div_eq_mul_inv, mul_comm]
    let γ : ℝ → Sphere3 := fun s => ⟨q s, by
      simpa only [Metric.mem_sphere, dist_zero_right] using hqnorm s⟩
    have hγ : Continuous γ := by
      apply Continuous.subtype_mk
      exact hq
    have hγ_zero : γ 0 = x := by
      apply Subtype.ext
      exact hq_zero
    have hne : (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)).NeBot := by
      rw [nhdsWithin_neBot]
      intro t ht
      rcases (Metric.mem_nhds_iff.mp ht) with ⟨ε, hε, hεt⟩
      refine ⟨ε / 2, hεt ?_, ?_⟩
      · simpa [Metric.mem_ball, dist_zero_right, abs_of_pos hε] using half_lt_self hε
      · exact half_pos hε
    letI : (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)).NeBot := hne
    refine mem_closure_of_tendsto (x := x) (s := A) (f := γ)
      (b := 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) ?_ ?_
    · have ht : Filter.Tendsto γ (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (γ 0)) :=
        hγ.continuousAt.tendsto.mono_left
          (show 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
      simpa [hγ_zero] using ht
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      have hpos : 0 < (q s) 0 := by
        rw [hqcoord s]
        exact div_pos hs (norm_pos_iff.mpr (hv_ne s))
      simpa [A] using hpos
  have hclosure : closure A = C := by
    apply Set.Subset.antisymm
    · apply closure_minimal
      · intro x hx
        have hx' : 0 < (x : E4) 0 := by simpa [A] using hx
        exact le_of_lt hx'
      · exact hclosed
    · intro x hx
      have hx' : 0 ≤ (x : E4) 0 := by simpa [C] using hx
      rcases lt_or_eq_of_le hx' with hxpos | hxzero
      · apply subset_closure
        simpa [A] using hxpos
      · exact hequator x hxzero.symm
  have hresult : frontier A = {x : Sphere3 | (x : E4) 0 = 0} := by
    rw [hopen.frontier_eq, hclosure]
    ext x
    constructor
    · intro hx
      have hxC : 0 ≤ (x : E4) 0 := by simpa [C] using hx.1
      have hxA : ¬ 0 < (x : E4) 0 := by simpa [A] using hx.2
      exact le_antisymm (le_of_not_gt hxA) hxC
    · intro hx
      have hxzero : (x : E4) 0 = 0 := by simpa using hx
      have hxC : x ∈ C := by simpa [C, hxzero]
      have hxA : x ∉ A := by simpa [A, hxzero]
      exact ⟨hxC, hxA⟩
  simpa [A] using hresult
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
