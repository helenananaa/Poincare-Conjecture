import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricInverseBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

/-- **Math.** uniform inverse ellipticity. -/
theorem uniform_inverse_ellipticity (A : E3 →L[ℝ] E3) (c K : ℝ) (hc : 0 < c) (hK : 0 < K)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hsym : ∀ v w : E3, inner ℝ (A v) w = inner ℝ v (A w))
    (hbound : ‖A‖ ≤ K) (xi : E3) :
    (c/K^2)*‖xi‖^2 ≤
      (∑ i : Fin 3, ∑ j : Fin 3, (A.inverse (EuclideanSpace.single j 1)) i * xi i * xi j) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, (A.inverse (EuclideanSpace.single j 1)) i * xi i * xi j) ≤
      (1/c)*‖xi‖^2 :=
/- SWARM_PROOF_BEGIN -/
by
  have hA_ne : A ≠ 0 := by
    intro hzero
    let e : E3 := EuclideanSpace.single (0 : Fin 3) 1
    have he : e ≠ 0 := by
      simp [e]
    have he_norm : 0 < ‖e‖ := norm_pos_iff.mpr he
    have h := hA e
    rw [hzero] at h
    simp at h
    nlinarith [sq_pos_of_pos he_norm]
  have hnormA : 0 < ‖A‖ := norm_pos_iff.mpr hA_ne
  have hquad := (symmetric_inverse_bounds A c hc hA hsym).2 xi
  have hxi : xi = ∑ j : Fin 3, xi j • EuclideanSpace.single j (1 : ℝ) := by
    simpa using ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.sum_repr xi).symm
  have hcoord (i : Fin 3) :
      (A.inverse xi) i = ∑ j : Fin 3, xi j * (A.inverse (EuclideanSpace.single j 1)) i := by
    have hmap := congrArg (fun y : E3 => (A.inverse y) i) hxi
    simp only [map_sum, map_smul] at hmap
    simpa [Finset.sum_apply, PiLp.smul_apply] using hmap
  have hcoeff :
      (∑ i : Fin 3, ∑ j : Fin 3,
        (A.inverse (EuclideanSpace.single j 1)) i * xi i * xi j) =
    inner ℝ (A.inverse xi) xi := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct]
    simp_rw [star_trivial, hcoord]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hden : c / K ^ 2 ≤ c / ‖A‖ ^ 2 := by
    have hsq : ‖A‖ ^ 2 ≤ K ^ 2 :=
      (sq_le_sq₀ (norm_nonneg A) (le_of_lt hK)).2 hbound
    have hrecip : 1 / K ^ 2 ≤ 1 / ‖A‖ ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos hnormA) hsq
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hrecip hc.le
  constructor
  · rw [hcoeff]
    exact (mul_le_mul_of_nonneg_right hden (sq_nonneg ‖xi‖)).trans hquad.1
  · rw [hcoeff]
    exact hquad.2
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
