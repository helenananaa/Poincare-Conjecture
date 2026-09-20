import Mathlib.Geometry.Manifold.SmoothEmbedding
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Exercise_4_10
import LeeSmoothLib.Ch04.Sec04_24.Proposition_4_22
import LeeSmoothLib.Ch04.Sec04_27.Problem_4_10
-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; local chapter precedent around
-- `sphereToRealProjectiveSpace` and descended smooth embeddings was checked directly.

open Manifold
open scoped ContDiff Manifold Matrix

noncomputable section

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "R4" => EuclideanSpace ℝ (Fin 4)

-- Pin the canonical standard-affine projective atlas.  Thus the covering theorem from Problem
-- 4.10 and every derivative below use definitionally the same charted-space structure.
local instance problem_4_13_canonical_projective_chartedSpace :
    ChartedSpace R2 (RealProjectiveSpace 2) :=
  realProjectiveSpaceChartedSpace 2

local instance problem_4_13_canonical_projective_isManifold :
    IsManifold (𝓡 2) (⊤ : WithTop ℕ∞) (RealProjectiveSpace 2) :=
  realProjectiveSpaceIsManifold 2

/-- Helper for the real-projective-plane embedding problem: the sphere-level map
`(x, y, z) ↦ (x² - y², xy, xz, yz)` from `S²` to `ℝ⁴`. -/
def real_projective_plane_embedding_lift :
    Metric.sphere (0 : R3) 1 → R4 :=
  fun p ↦
    let x := (p : R3) 0
    let y := (p : R3) 1
    let z := (p : R3) 2
    EuclideanSpace.single 0 (x ^ (2 : ℕ) - y ^ (2 : ℕ)) +
      EuclideanSpace.single 1 (x * y) +
      EuclideanSpace.single 2 (x * z) +
      EuclideanSpace.single 3 (y * z)

/-- Helper for the real-projective-plane embedding problem: the sphere-level lift has the stated
coordinate formula. -/
theorem real_projective_plane_embedding_lift_apply
    (p : Metric.sphere (0 : R3) 1) :
    real_projective_plane_embedding_lift p =
      EuclideanSpace.single 0 (((p : R3) 0) ^ (2 : ℕ) - ((p : R3) 1) ^ (2 : ℕ)) +
        EuclideanSpace.single 1 (((p : R3) 0) * ((p : R3) 1)) +
        EuclideanSpace.single 2 (((p : R3) 0) * ((p : R3) 2)) +
        EuclideanSpace.single 3 (((p : R3) 1) * ((p : R3) 2)) := by
  rfl

private def ambient : R3 → R4 := fun p ↦
  EuclideanSpace.single 0 (p 0 ^ (2 : ℕ) - p 1 ^ (2 : ℕ)) +
    EuclideanSpace.single 1 (p 0 * p 1) +
    EuclideanSpace.single 2 (p 0 * p 2) +
    EuclideanSpace.single 3 (p 1 * p 2)

private theorem ambient_contMDiff : ContMDiff (𝓡 3) (𝓡 4) ∞ ambient := by
  rw [contMDiff_iff_contDiff]
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp [ambient] <;> fun_prop

private theorem fderiv_coord_apply {F : R3 → R4} {p v : R3}
    (hF : DifferentiableAt ℝ F p) (i : Fin 4) :
    (fderiv ℝ F p v) i = fderiv ℝ (fun q : R3 ↦ F q i) p v := by
  have hcoord :
      HasFDerivAt (fun q : R3 ↦ F q i)
        ((PiLp.proj 2 (fun _ : Fin 4 ↦ ℝ) i).comp (fderiv ℝ F p)) p :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 4 ↦ ℝ) (F p) i).comp p
      hF.hasFDerivAt
  rw [hcoord.fderiv]
  rfl

private theorem fderiv_sq_sub_sq_apply (p v : R3) :
    fderiv ℝ (fun q : R3 ↦ q 0 ^ (2 : ℕ) - q 1 ^ (2 : ℕ)) p v =
      2 * p 0 * v 0 - 2 * p 1 * v 1 := by
  have h0 :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 0).pow 2
  have h1 :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 1).pow 2
  change fderiv ℝ ((fun q : R3 ↦ q 0 ^ (2 : ℕ)) -
    fun q : R3 ↦ q 1 ^ (2 : ℕ)) p v = _
  rw [(h0.sub h1).fderiv]
  simp only [sub_apply, smul_apply, PiLp.proj_apply, smul_eq_mul]
  ring

private theorem fderiv_mul_apply (p v : R3) (i j : Fin 3) :
    fderiv ℝ (fun q : R3 ↦ q i * q j) p v = p j * v i + p i * v j := by
  have hi := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p i
  have hj := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p j
  change fderiv ℝ ((fun q : R3 ↦ q i) * fun q : R3 ↦ q j) p v = _
  rw [(hi.mul hj).fderiv]
  simp only [add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul]
  ring

private theorem ambient_fderiv_apply (p v : R3) :
    fderiv ℝ ambient p v =
      EuclideanSpace.single 0 (2 * p 0 * v 0 - 2 * p 1 * v 1) +
        EuclideanSpace.single 1 (p 1 * v 0 + p 0 * v 1) +
        EuclideanSpace.single 2 (p 2 * v 0 + p 0 * v 2) +
        EuclideanSpace.single 3 (p 2 * v 1 + p 1 * v 2) := by
  ext i
  fin_cases i
  · rw [fderiv_coord_apply
        (ambient_contMDiff.contDiff.differentiable (by simp)).differentiableAt]
    simp only [ambient, PiLp.add_apply, PiLp.single_apply]
    simp
    change fderiv ℝ (fun q : R3 ↦ q 0 ^ (2 : ℕ) - q 1 ^ (2 : ℕ)) p v =
      2 * p 0 * v 0 - 2 * p 1 * v 1
    exact fderiv_sq_sub_sq_apply p v
  · rw [fderiv_coord_apply
        (ambient_contMDiff.contDiff.differentiable (by simp)).differentiableAt]
    simp only [ambient, PiLp.add_apply, PiLp.single_apply]
    simp
    change fderiv ℝ (fun q : R3 ↦ q 0 * q 1) p v = p 1 * v 0 + p 0 * v 1
    exact fderiv_mul_apply p v 0 1
  · rw [fderiv_coord_apply
        (ambient_contMDiff.contDiff.differentiable (by simp)).differentiableAt]
    simp only [ambient, PiLp.add_apply, PiLp.single_apply]
    simp
    change fderiv ℝ (fun q : R3 ↦ q 0 * q 2) p v = p 2 * v 0 + p 0 * v 2
    exact fderiv_mul_apply p v 0 2
  · rw [fderiv_coord_apply
        (ambient_contMDiff.contDiff.differentiable (by simp)).differentiableAt]
    simp only [ambient, PiLp.add_apply, PiLp.single_apply]
    simp
    change fderiv ℝ (fun q : R3 ↦ q 1 * q 2) p v = p 2 * v 1 + p 1 * v 2
    exact fderiv_mul_apply p v 1 2

private theorem sphere_coordinate_sq_sum (p : Metric.sphere (0 : R3) 1) :
    (p : R3) 0 ^ (2 : ℕ) + (p : R3) 1 ^ (2 : ℕ) + (p : R3) 2 ^ (2 : ℕ) = 1 := by
  have hnorm := EuclideanSpace.real_norm_sq_eq (p : R3)
  rw [mem_sphere_zero_iff_norm.mp p.property] at hnorm
  simp [Fin.sum_univ_succ] at hnorm
  nlinarith

private theorem ambient_fderiv_injective_on_tangent
    (p : Metric.sphere (0 : R3) 1) (v : R3)
    (hv_tangent : @inner ℝ R3 _ (p : R3) v = 0)
    (hv : fderiv ℝ ambient (p : R3) v = 0) : v = 0 := by
  have h0 : 2 * (p : R3) 0 * v 0 - 2 * (p : R3) 1 * v 1 = 0 := by
    have := congrArg (fun w : R4 ↦ w 0) hv
    simpa [ambient_fderiv_apply] using this
  have h1 : (p : R3) 1 * v 0 + (p : R3) 0 * v 1 = 0 := by
    have := congrArg (fun w : R4 ↦ w 1) hv
    simpa [ambient_fderiv_apply] using this
  have h2 : (p : R3) 2 * v 0 + (p : R3) 0 * v 2 = 0 := by
    have := congrArg (fun w : R4 ↦ w 2) hv
    simpa [ambient_fderiv_apply] using this
  have h3 : (p : R3) 2 * v 1 + (p : R3) 1 * v 2 = 0 := by
    have := congrArg (fun w : R4 ↦ w 3) hv
    simpa [ambient_fderiv_apply] using this
  have htangent :
      (p : R3) 0 * v 0 + (p : R3) 1 * v 1 + (p : R3) 2 * v 2 = 0 := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ] at hv_tangent
    nlinarith
  have hp := sphere_coordinate_sq_sum p
  by_cases hs : (p : R3) 0 ^ (2 : ℕ) + (p : R3) 1 ^ (2 : ℕ) = 0
  · have hx : (p : R3) 0 = 0 := by nlinarith [sq_nonneg ((p : R3) 0), sq_nonneg ((p : R3) 1)]
    have hy : (p : R3) 1 = 0 := by nlinarith [sq_nonneg ((p : R3) 0), sq_nonneg ((p : R3) 1)]
    have hz : (p : R3) 2 ≠ 0 := by
      intro hz
      simp [hx, hy, hz] at hp
    have hv0 : v 0 = 0 := by
      exact (mul_eq_zero.mp (by simpa [hx] using h2)).resolve_left hz
    have hv1 : v 1 = 0 := by
      exact (mul_eq_zero.mp (by simpa [hy] using h3)).resolve_left hz
    have hv2 : v 2 = 0 := by
      exact (mul_eq_zero.mp (by simpa [hx, hy] using htangent)).resolve_left hz
    ext i
    fin_cases i <;> simp [hv0, hv1, hv2]

  · have hspos : 0 < (p : R3) 0 ^ (2 : ℕ) + (p : R3) 1 ^ (2 : ℕ) := by
      have hsnonneg : 0 ≤ (p : R3) 0 ^ (2 : ℕ) + (p : R3) 1 ^ (2 : ℕ) := by positivity
      exact lt_of_le_of_ne hsnonneg (Ne.symm hs)
    have h0x := congrArg (fun t : ℝ ↦ (p : R3) 0 * t) h0
    have h1y := congrArg (fun t : ℝ ↦ 2 * (p : R3) 1 * t) h1
    have hv0scaled :
        ((p : R3) 0 ^ (2 : ℕ) + (p : R3) 1 ^ (2 : ℕ)) * v 0 = 0 := by
      nlinarith
    have hv0 : v 0 = 0 := (mul_eq_zero.mp hv0scaled).resolve_left (ne_of_gt hspos)
    have h0y := congrArg (fun t : ℝ ↦ (p : R3) 1 * t) h0
    have h1x := congrArg (fun t : ℝ ↦ 2 * (p : R3) 0 * t) h1
    have hv1scaled :
        ((p : R3) 0 ^ (2 : ℕ) + (p : R3) 1 ^ (2 : ℕ)) * v 1 = 0 := by
      nlinarith
    have hv1 : v 1 = 0 := (mul_eq_zero.mp hv1scaled).resolve_left (ne_of_gt hspos)
    have hxv2 : (p : R3) 0 * v 2 = 0 := by simpa [hv0] using h2
    have hyv2 : (p : R3) 1 * v 2 = 0 := by simpa [hv1] using h3
    have hv2 : v 2 = 0 := by
      by_contra hv2
      have hx : (p : R3) 0 = 0 := (mul_eq_zero.mp hxv2).resolve_right hv2
      have hy : (p : R3) 1 = 0 := (mul_eq_zero.mp hyv2).resolve_right hv2
      simp [hx, hy] at hspos
    ext i
    fin_cases i <;> simp [hv0, hv1, hv2]

private def lift : Metric.sphere (0 : R3) 1 → R4 := fun p ↦ ambient (p : R3)

private theorem lift_contMDiff : ContMDiff (𝓡 2) (𝓡 4) ∞ lift := by
  haveI : Fact (Module.finrank ℝ R3 = 2 + 1) := Fact.mk finrank_euclideanSpace_fin
  exact ambient_contMDiff.comp contMDiff_coe_sphere

private theorem lift_isImmersion : IsImmersion (𝓡 2) (𝓡 4) ∞ lift := by
  haveI : Fact (Module.finrank ℝ R3 = 2 + 1) := Fact.mk finrank_euclideanSpace_fin
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv lift_contMDiff).2 ?_
  intro p u v huv
  let L : TangentSpace (𝓡 2) p →L[ℝ] R3 :=
    mfderiv (𝓡 2) (𝓡 3) ((↑) : Metric.sphere (0 : R3) 1 → R3) p
  have hchain :
      mfderiv (𝓡 2) (𝓡 4) lift p =
        (fderiv ℝ ambient (p : R3)).comp L := by
    change mfderiv (𝓡 2) (𝓡 4)
      (ambient ∘ ((↑) : Metric.sphere (0 : R3) 1 → R3)) p = _
    have hamb : MDifferentiableAt (𝓡 3) (𝓡 4) ambient (p : R3) :=
      ambient_contMDiff.mdifferentiableAt (by simp)
    have hcoe : MDifferentiableAt (𝓡 2) (𝓡 3)
        ((↑) : Metric.sphere (0 : R3) 1 → R3) p :=
      (contMDiff_coe_sphere :
        ContMDiff (𝓡 2) (𝓡 3) ∞
          ((↑) : Metric.sphere (0 : R3) 1 → R3)).mdifferentiableAt (by simp)
    simpa [L, mfderiv_eq_fderiv] using mfderiv_comp p hamb hcoe
  rw [hchain] at huv
  change fderiv ℝ ambient (p : R3) (L u) =
    fderiv ℝ ambient (p : R3) (L v) at huv
  have hw_deriv : fderiv ℝ ambient (p : R3) (L (u - v)) = 0 := by
    rw [map_sub, map_sub, huv, sub_self]
  have hw_range : L (u - v) ∈
      (mfderiv (𝓡 2) (𝓡 3)
        ((↑) : Metric.sphere (0 : R3) 1 → R3) p).range := by
    exact ⟨u - v, rfl⟩
  rw [range_mfderiv_coe_sphere p] at hw_range
  have hw_tangent : @inner ℝ R3 _ (p : R3) (L (u - v)) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw_range
  have hw_zero := ambient_fderiv_injective_on_tangent p (L (u - v)) hw_tangent hw_deriv
  have hL_zero : L (u - v) = L 0 := by simpa using hw_zero
  have huv_zero : u - v = 0 := (mfderiv_coe_sphere_injective p) hL_zero
  exact sub_eq_zero.mp huv_zero

private theorem lift_neg (p : Metric.sphere (0 : R3) 1) : lift (-p) = lift p := by
  ext i
  fin_cases i <;> simp [lift, ambient]

set_option maxHeartbeats 600000 in
private theorem lift_eq_iff_eq_or_eq_neg
    (p q : Metric.sphere (0 : R3) 1) :
    lift p = lift q ↔ q = p ∨ q = -p := by
  constructor
  · intro hpq
    have hA : (p : R3) 0 ^ (2 : ℕ) - (p : R3) 1 ^ (2 : ℕ) =
        (q : R3) 0 ^ (2 : ℕ) - (q : R3) 1 ^ (2 : ℕ) := by
      simpa [lift, ambient] using congrArg (fun w : R4 ↦ w 0) hpq
    have hB : (p : R3) 0 * (p : R3) 1 = (q : R3) 0 * (q : R3) 1 := by
      simpa [lift, ambient] using congrArg (fun w : R4 ↦ w 1) hpq
    have hC : (p : R3) 0 * (p : R3) 2 = (q : R3) 0 * (q : R3) 2 := by
      simpa [lift, ambient] using congrArg (fun w : R4 ↦ w 2) hpq
    have hD : (p : R3) 1 * (p : R3) 2 = (q : R3) 1 * (q : R3) 2 := by
      simpa [lift, ambient] using congrArg (fun w : R4 ↦ w 3) hpq
    have hsum_sq :
        ((p : R3) 0 ^ (2 : ℕ) + (p : R3) 1 ^ (2 : ℕ)) ^ (2 : ℕ) =
          ((q : R3) 0 ^ (2 : ℕ) + (q : R3) 1 ^ (2 : ℕ)) ^ (2 : ℕ) := by
      calc
        ((p : R3) 0 ^ (2 : ℕ) + (p : R3) 1 ^ (2 : ℕ)) ^ (2 : ℕ) =
            ((p : R3) 0 ^ (2 : ℕ) - (p : R3) 1 ^ (2 : ℕ)) ^ (2 : ℕ) +
              4 * ((p : R3) 0 * (p : R3) 1) ^ (2 : ℕ) := by ring
        _ = ((q : R3) 0 ^ (2 : ℕ) - (q : R3) 1 ^ (2 : ℕ)) ^ (2 : ℕ) +
              4 * ((q : R3) 0 * (q : R3) 1) ^ (2 : ℕ) := by rw [hA, hB]
        _ = ((q : R3) 0 ^ (2 : ℕ) + (q : R3) 1 ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    have hsum :
        (p : R3) 0 ^ (2 : ℕ) + (p : R3) 1 ^ (2 : ℕ) =
          (q : R3) 0 ^ (2 : ℕ) + (q : R3) 1 ^ (2 : ℕ) := by
      have hpnonneg : 0 ≤ (p : R3) 0 ^ (2 : ℕ) + (p : R3) 1 ^ (2 : ℕ) := by positivity
      have hqnonneg : 0 ≤ (q : R3) 0 ^ (2 : ℕ) + (q : R3) 1 ^ (2 : ℕ) := by positivity
      rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsum_sq with h | h
      · exact h
      · nlinarith
    have hx_sq : (p : R3) 0 ^ (2 : ℕ) = (q : R3) 0 ^ (2 : ℕ) := by nlinarith
    have hy_sq : (p : R3) 1 ^ (2 : ℕ) = (q : R3) 1 ^ (2 : ℕ) := by nlinarith
    have hpunit := sphere_coordinate_sq_sum p
    have hqunit := sphere_coordinate_sq_sum q
    have hz_sq : (p : R3) 2 ^ (2 : ℕ) = (q : R3) 2 ^ (2 : ℕ) := by nlinarith
    by_cases hx : (p : R3) 0 = 0
    · have hqx : (q : R3) 0 = 0 := by nlinarith
      by_cases hy : (p : R3) 1 = 0
      · have hqy : (q : R3) 1 = 0 := by nlinarith
        rcases eq_or_eq_neg_of_sq_eq_sq ((q : R3) 2) ((p : R3) 2) hz_sq.symm with hz | hz
        · left
          apply Subtype.ext
          ext i
          fin_cases i <;> simp [hx, hqx, hy, hqy, hz]
        · right
          apply Subtype.ext
          ext i
          fin_cases i <;> simp [hx, hqx, hy, hqy, hz]
      · rcases eq_or_eq_neg_of_sq_eq_sq ((q : R3) 1) ((p : R3) 1) hy_sq.symm with hy' | hy'
        · have hz' : (q : R3) 2 = (p : R3) 2 := by
            apply mul_left_cancel₀ hy
            simpa [hy'] using hD.symm
          left
          apply Subtype.ext
          ext i
          fin_cases i <;> simp [hx, hqx, hy', hz']
        · have hqy : (q : R3) 1 = -(p : R3) 1 := hy'
          have hz' : (q : R3) 2 = -(p : R3) 2 := by
            apply mul_left_cancel₀ hy
            have hD' := hD
            rw [hqy] at hD'
            nlinarith
          right
          apply Subtype.ext
          ext i
          fin_cases i <;> simp [hx, hqx, hqy, hz']
    · rcases eq_or_eq_neg_of_sq_eq_sq ((q : R3) 0) ((p : R3) 0) hx_sq.symm with hx' | hx'
      · have hy' : (q : R3) 1 = (p : R3) 1 := by
          apply mul_left_cancel₀ hx
          simpa [hx'] using hB.symm
        have hz' : (q : R3) 2 = (p : R3) 2 := by
          apply mul_left_cancel₀ hx
          simpa [hx'] using hC.symm
        left
        apply Subtype.ext
        ext i
        fin_cases i <;> simp [hx', hy', hz']
      · have hqx : (q : R3) 0 = -(p : R3) 0 := hx'
        have hy' : (q : R3) 1 = -(p : R3) 1 := by
          apply mul_left_cancel₀ hx
          have hB' := hB
          rw [hqx] at hB'
          nlinarith
        have hz' : (q : R3) 2 = -(p : R3) 2 := by
          apply mul_left_cancel₀ hx
          have hC' := hC
          rw [hqx] at hC'
          nlinarith
        right
        apply Subtype.ext
        ext i
        fin_cases i <;> simp [hqx, hy', hz']
  · rintro (rfl | rfl)
    · rfl
    · exact (lift_neg p).symm

private def descended : RealProjectiveSpace 2 → R4 := fun x ↦
  lift (Function.surjInv (sphereToRealProjectiveSpace_surjective 2) x)

private theorem descended_comp (p : Metric.sphere (0 : R3) 1) :
    descended (sphereToRealProjectiveSpace 2 p) = lift p := by
  apply (lift_eq_iff_eq_or_eq_neg _ _).2
  apply (same_projective_point_on_unit_sphere_iff_eq_or_eq_neg 2 _ _).1
  exact Function.surjInv_eq (sphereToRealProjectiveSpace_surjective 2) _

private theorem descended_contMDiff : ContMDiff (𝓡 2) (𝓡 4) ∞ descended := by
  let hcov := sphere_to_realProjectiveSpace_isSmoothCoveringMap 2
  refine (smooth_iff_comp_right_of_surjective_isLocalDiffeomorph
    hcov.isLocalDiffeomorph hcov.surjective).2 ?_
  have hcomp : descended ∘ sphereToRealProjectiveSpace 2 = lift := by
    funext p
    exact descended_comp p
  rw [hcomp]
  exact lift_contMDiff

private theorem injective_of_comp_right {α β γ : Type*} {f : β → γ} {g : α → β}
    (hcomp : Function.Injective (f ∘ g)) (hg : Function.Surjective g) :
    Function.Injective f := by
  intro x y hxy
  rcases hg x with ⟨a, rfl⟩
  rcases hg y with ⟨b, rfl⟩
  exact congrArg g (hcomp hxy)

private theorem descended_isImmersion : IsImmersion (𝓡 2) (𝓡 4) ∞ descended := by
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv descended_contMDiff).2 ?_
  intro x
  let hcov := sphere_to_realProjectiveSpace_isSmoothCoveringMap 2
  rcases hcov.surjective x with ⟨p, rfl⟩
  have hq_surj : Function.Surjective
      (mfderiv (𝓡 2) (𝓡 2) (sphereToRealProjectiveSpace 2) p) := by
    rw [← hcov.isLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe (by simp) p]
    exact (hcov.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) p).surjective
  have hchain :
      mfderiv (𝓡 2) (𝓡 4) lift p =
        (mfderiv (𝓡 2) (𝓡 4) descended (sphereToRealProjectiveSpace 2 p)).comp
          (mfderiv (𝓡 2) (𝓡 2) (sphereToRealProjectiveSpace 2) p) := by
    have hdesc : MDifferentiableAt (𝓡 2) (𝓡 4) descended
        (sphereToRealProjectiveSpace 2 p) :=
      descended_contMDiff.mdifferentiableAt (by simp)
    have hq : MDifferentiableAt (𝓡 2) (𝓡 2) (sphereToRealProjectiveSpace 2) p :=
      hcov.isLocalDiffeomorph.contMDiff.mdifferentiableAt (by simp)
    have hcomp : descended ∘ sphereToRealProjectiveSpace 2 = lift := by
      funext z
      exact descended_comp z
    rw [← hcomp]
    exact mfderiv_comp p hdesc hq
  have hlift_inj : Function.Injective (mfderiv (𝓡 2) (𝓡 4) lift p) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv lift_contMDiff).1 lift_isImmersion p
  have hcomp_inj : Function.Injective
      ((mfderiv (𝓡 2) (𝓡 4) descended (sphereToRealProjectiveSpace 2 p)).comp
        (mfderiv (𝓡 2) (𝓡 2) (sphereToRealProjectiveSpace 2) p)) := by
    rw [← hchain]
    exact hlift_inj
  exact injective_of_comp_right hcomp_inj hq_surj

private theorem descended_injective : Function.Injective descended := by
  intro x y hxy
  rcases sphereToRealProjectiveSpace_surjective 2 x with ⟨p, rfl⟩
  rcases sphereToRealProjectiveSpace_surjective 2 y with ⟨q, rfl⟩
  have hlift : lift p = lift q := by
    rw [← descended_comp p, ← descended_comp q]
    exact hxy
  exact (same_projective_point_on_unit_sphere_iff_eq_or_eq_neg 2 p q).2
    ((lift_eq_iff_eq_or_eq_neg p q).1 hlift)

private theorem descended_isSmoothEmbedding :
    IsSmoothEmbedding (𝓡 2) (𝓡 4) ∞ descended := by
  letI : CompactSpace (RealProjectiveSpace 2) := by
    have hrange : Set.range (sphereToRealProjectiveSpace 2) = Set.univ :=
      Set.range_eq_univ.mpr (sphereToRealProjectiveSpace_surjective 2)
    have hcompact : IsCompact (Set.univ : Set (RealProjectiveSpace 2)) := by
      simpa [hrange] using isCompact_range (sphereToRealProjectiveSpace_continuous 2)
    exact isCompact_univ_iff.mp hcompact
  exact smooth_embedding_of_compact_source_injective_isImmersion
    descended_injective descended_isImmersion

/-- Problem 4-13: the map `(x, y, z) ↦ (x² - y², xy, xz, yz)` on `S²` descends through the
quotient map `sphereToRealProjectiveSpace 2 : S² → ℝP²` to a smooth embedding of `ℝP²` into
`ℝ⁴`.

The projective charted-space structure is pinned above to the canonical standard-affine atlas.
The endpoint asserts the required `C^∞` smooth embedding, without strengthening its conclusion to
analytic regularity. -/
theorem real_projective_plane_exists_isSmoothEmbedding_to_R4 :
    ∃ f : RealProjectiveSpace 2 → R4,
      ((∀ p : Metric.sphere (0 : R3) 1,
          f (sphereToRealProjectiveSpace 2 p) = real_projective_plane_embedding_lift p) ∧
        Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 4) (∞ : WithTop ℕ∞) f) := by
  refine ⟨descended, ?_, descended_isSmoothEmbedding⟩
  intro p
  exact descended_comp p

#print axioms real_projective_plane_exists_isSmoothEmbedding_to_R4
