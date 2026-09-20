import PoincareConjecture.ParallelMath.Core
import PoincareConjecture.ParallelMath.Variational.QuadraticDiscriminant

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath
open Set Matrix
open scoped BigOperators

/-- Three-dimensional Gram-determinant comparison: if a symmetric 3×3 form
satisfies `(1-ε)|v|² ≤ G(v,v) ≤ (1+ε)|v|²` for every coordinate vector, then
its determinant (the squared volume Jacobian on an orthonormal triple) obeys

  `(1-ε)³ ≤ det G ≤ (1+ε)³`.

The square-root form used for volume densities is recorded as a corollary.
This is the n=3 analogue of `plane_area_distortion`. No manifold, no
`EpsilonClose`, and no injectivity-radius content. -/
theorem volume_form_det_distortion (G : Fin 3 → Fin 3 → ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hsym : ∀ i j : Fin 3, G i j = G j i)
    (h : ∀ v : Fin 3 → ℝ,
      (1 - ε) * ∑ i, (v i) ^ 2 ≤ quadraticForm G v ∧
      quadraticForm G v ≤ (1 + ε) * ∑ i, (v i) ^ 2) :
    (1 - ε) ^ 3 ≤ (of (fun i j : Fin 3 => G i j)).det ∧
    (of (fun i j : Fin 3 => G i j)).det ≤ (1 + ε) ^ 3 :=
/- SWARM_PROOF_BEGIN -/
by
  set A : Matrix (Fin 3) (Fin 3) ℝ := fun i j => G i j
  have hHerm : A.IsHermitian :=
    IsHermitian.ext fun i j => by simpa [A, star_trivial] using hsym j i
  have hqf (v : Fin 3 → ℝ) : quadraticForm G v = v ⬝ᵥ (A *ᵥ v) := by
    unfold quadraticForm
    rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have h1me : 0 ≤ 1 - ε := sub_nonneg.mpr hε1.le
  have _ := add_nonneg (zero_le_one : (0 : ℝ) ≤ 1) hε0
  have heigs (i : Fin 3) :
      1 - ε ≤ hHerm.eigenvalues i ∧ hHerm.eigenvalues i ≤ 1 + ε := by
    let v : Fin 3 → ℝ := ⇑(hHerm.eigenvectorBasis i)
    have hunit : ∑ k, (v k) ^ 2 = 1 := by
      have hnorm : ‖hHerm.eigenvectorBasis i‖ = 1 :=
        hHerm.eigenvectorBasis.orthonormal.1 i
      have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (hHerm.eigenvectorBasis i)
      rw [hnorm, one_pow] at hsq
      simp_rw [Real.norm_eq_abs, sq_abs] at hsq
      simpa [v] using hsq.symm
    have heig : hHerm.eigenvalues i = quadraticForm G v := by
      rw [hHerm.eigenvalues_eq, hqf]
      simp [v, star_trivial, RCLike.re_to_real]
    have hb := h v
    rw [← heig, hunit, mul_one, mul_one] at hb
    exact hb
  have hdetA : A.det = ∏ i, hHerm.eigenvalues i := by
    simpa using hHerm.det_eq_prod_eigenvalues
  change (1 - ε) ^ 3 ≤ A.det ∧ A.det ≤ (1 + ε) ^ 3
  rw [hdetA]
  constructor
  · calc
      (1 - ε) ^ 3 = ∏ _i : Fin 3, (1 - ε) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i, hHerm.eigenvalues i :=
        Finset.prod_le_prod (fun _ _ => h1me) (fun i _ => (heigs i).1)
  · calc
      ∏ i, hHerm.eigenvalues i ≤ ∏ _i : Fin 3, (1 + ε) :=
        Finset.prod_le_prod (fun i _ => h1me.trans (heigs i).1) (fun i _ => (heigs i).2)
      _ = (1 + ε) ^ 3 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
/- SWARM_PROOF_END -/

theorem volume_form_jacobian_distortion (G : Fin 3 → Fin 3 → ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hsym : ∀ i j : Fin 3, G i j = G j i)
    (h : ∀ v : Fin 3 → ℝ,
      (1 - ε) * ∑ i, (v i) ^ 2 ≤ quadraticForm G v ∧
      quadraticForm G v ≤ (1 + ε) * ∑ i, (v i) ^ 2) :
    (1 - ε) ^ ((3 : ℝ) / 2) ≤ Real.sqrt (of (fun i j : Fin 3 => G i j)).det ∧
    Real.sqrt (of (fun i j : Fin 3 => G i j)).det ≤ (1 + ε) ^ ((3 : ℝ) / 2) :=
/- SWARM_PROOF_BEGIN -/
by
  have hdet := volume_form_det_distortion G ε hε0 hε1 hsym h
  have h1me : 0 ≤ 1 - ε := sub_nonneg.mpr hε1.le
  have h1pe : 0 ≤ 1 + ε := add_nonneg zero_le_one hε0
  have hcube {a : ℝ} (ha : 0 ≤ a) :
      Real.sqrt (a ^ 3) = a ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul ha 3 (1 / (2 : ℝ))]
    congr 1
    ring
  constructor
  · have hs := Real.sqrt_le_sqrt hdet.1
    rwa [hcube h1me] at hs
  · have hs := Real.sqrt_le_sqrt hdet.2
    rwa [hcube h1pe] at hs
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath
