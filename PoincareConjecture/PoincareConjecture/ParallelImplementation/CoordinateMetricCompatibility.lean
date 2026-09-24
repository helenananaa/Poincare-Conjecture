import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateMetricCompatibility
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped BigOperators
theorem coordinate_metric_compatibility
    (g h : Mat) (d : First)
    (hgh : ∀ i j : Idx, (∑ k : Idx, g i k*h k j) = if i=j then 1 else 0)
    (hd : ∀ a i j : Idx, d a i j=d a j i) :
    ∀ i j k : Idx,
      (∑ l : Idx, g k l*christoffel h d l i j)+
      (∑ l : Idx, g j l*christoffel h d l i k)=d i j k :=
/- SWARM_PROOF_BEGIN -/
by
  have hc (a : Idx) (f : Idx → ℝ) :
      (∑ l : Idx, g a l*(∑ r : Idx, h l r*f r))=f a := by
    calc
      (∑ l : Idx, g a l*(∑ r : Idx, h l r*f r)) =
          ∑ l : Idx, ∑ r : Idx, (g a l*h l r)*f r := by
            simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ r : Idx, (∑ l : Idx, g a l*h l r)*f r := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = f a := by simp [hgh]
  intro i j k
  change (∑ l : Idx, g k l*(∑ r : Idx, h l r*lowerChristoffel d r i j))+
    (∑ l : Idx, g j l*(∑ r : Idx, h l r*lowerChristoffel d r i k))=d i j k
  rw [hc k, hc j]
  dsimp [lowerChristoffel]
  rw [hd i k j]
  ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateMetricCompatibility
