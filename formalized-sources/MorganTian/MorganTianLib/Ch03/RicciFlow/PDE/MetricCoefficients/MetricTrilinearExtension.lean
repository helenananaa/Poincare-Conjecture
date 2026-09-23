import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Equality of the two trilinear metric expressions follows from equality on a basis. -/
theorem metric_trilinear_extension (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (B : E3 →L[ℝ] E3 →L[ℝ] E3)
    (hbasis : ∀ r i j : Fin 3,
      inner ℝ (P r (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1) =
        inner ℝ (A (B (EuclideanSpace.single r 1) (EuclideanSpace.single i 1)))
          (EuclideanSpace.single j 1) +
        inner ℝ (A (EuclideanSpace.single i 1))
          (B (EuclideanSpace.single r 1) (EuclideanSpace.single j 1)))
    (X Y Z : E3) :
    inner ℝ ((∑ r : Fin 3, X r • P r) Y) Z =
      inner ℝ (A (B X Y)) Z + inner ℝ (A Y) (B X Z) :=
/- SWARM_PROOF_BEGIN -/
by
  have hcoord (i : Fin 3) :
      (∑ r : Fin 3, X r • EuclideanSpace.single r (1 : ℝ)) i = X i := by
    simpa using congrArg (fun v : E3 => v i)
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr X)
  have hcoord' (i : Fin 3) :
      (∑ r : Fin 3, X.ofLp r • Pi.single r (1 : ℝ)) i = X.ofLp i := by
    simpa using hcoord i
  rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr X,
    ← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr Y,
    ← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr Z]
  simp only [map_sum, map_smul, sum_apply, smul_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single]
  simp only [hcoord']
  simp_rw [hbasis]
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have sumOrder (f : Fin 3 → Fin 3 → Fin 3 → ℝ) :
      (∑ j : Fin 3, ∑ i : Fin 3, ∑ r : Fin 3, f r i j) =
        ∑ r : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, f r i j := by
    calc
      _ = ∑ j : Fin 3, ∑ r : Fin 3, ∑ i : Fin 3, f r i j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Finset.sum_comm
      _ = ∑ r : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, f r i j := by
        exact Finset.sum_comm
      _ = ∑ r : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, f r i j := by
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.sum_comm
  congr 1
  rw [sumOrder (fun r i j =>
        Z.ofLp j * (Y.ofLp i * (X.ofLp r *
          inner ℝ (A (EuclideanSpace.single i 1))
            (B (EuclideanSpace.single r 1) (EuclideanSpace.single j 1))))),
      sumOrder (fun r i j =>
        Z.ofLp j * (X.ofLp r * (Y.ofLp i *
          inner ℝ (A (EuclideanSpace.single i 1))
            (B (EuclideanSpace.single r 1) (EuclideanSpace.single j 1)))))]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
