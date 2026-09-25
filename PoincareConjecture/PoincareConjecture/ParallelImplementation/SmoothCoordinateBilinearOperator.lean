import Mathlib
import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothCoordinateBilinearOperator
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_smooth_coordinate_bilinear_operator
    (s : Set E3) (b : E3 → (E3 →ₗ[ℝ] E3 →ₗ[ℝ] ℝ))
    (hb : ∀ i j : Fin 3, ContDiffOn ℝ ∞
      (fun x => b x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) s) :

    ∃ A : E3 → (E3 →L[ℝ] E3), ContDiffOn ℝ ∞ A s ∧
      ∀ x v w : E3, inner ℝ (A x v) w=b x v w :=
/- SWARM_PROOF_BEGIN -/
by
  let e : Fin 3 → E3 := fun i => EuclideanSpace.single i 1
  let A : E3 → E3 →L[ℝ] E3 := fun x =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      b x (e i) (e j) • (innerSL ℝ (e i)).smulRight (e j)
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    apply ContDiffOn.sum
    intro i hi
    apply ContDiffOn.sum
    intro j hj
    exact (hb i j).smul_const ((innerSL ℝ (e i)).smulRight (e j))
  · intro x v w
    have hv : v = ∑ i : Fin 3, v i • e i := by
      simpa [e] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v).symm
    have hw : w = ∑ j : Fin 3, w j • e j := by
      simpa [e] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w).symm
    have hbilin : b x v w =
        ∑ i : Fin 3, ∑ j : Fin 3, (v i * w j) * b x (e i) (e j) := by
      conv_lhs => rw [hv, hw]
      simp only [map_sum, map_smul]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    calc
      inner ℝ (A x v) w =
          ∑ i : Fin 3, ∑ j : Fin 3,
            (b x (e i) (e j)) * (v i * w j) := by
        simp [A, e, sum_inner, real_inner_smul_left, innerSL_apply_apply,
          EuclideanSpace.inner_single_left, mul_assoc, mul_comm]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, (v i * w j) * b x (e i) (e j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = b x v w := hbilin.symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothCoordinateBilinearOperator
