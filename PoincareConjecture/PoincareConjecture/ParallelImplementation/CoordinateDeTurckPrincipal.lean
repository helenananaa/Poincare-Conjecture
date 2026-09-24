import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateDeTurckPrincipal
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped BigOperators
theorem coordinate_deturck_principal
    (g h : Mat) (dd : Second)
    (hg : ∀ i j : Idx, g i j=g j i)
    (hh : ∀ i j : Idx, h i j=h j i)
    (hgh : ∀ i j : Idx, (∑ k : Idx, g i k*h k j) = if i=j then 1 else 0)
    (hcomm : ∀ a b i j : Idx, dd a b i j=dd b a i j) :
    ∀ i j : Idx, liePrincipal g h dd i j =
      ∑ a : Idx, ∑ b : Idx, h a b*
        (dd a i b j+dd a j b i-dd i j a b) :=
/- SWARM_PROOF_BEGIN -/
by
  have hc (a : Idx) (f : Idx → ℝ) :
      (∑ k : Idx, g a k*(∑ l : Idx, h k l*f l))=f a := by
    calc
      (∑ k : Idx, g a k*(∑ l : Idx, h k l*f l)) =
          ∑ k : Idx, ∑ l : Idx, (g a k*h k l)*f l := by
            simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ l : Idx, (∑ k : Idx, g a k*h k l)*f l := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = f a := by simp [hgh]
  have hv (a k : Idx) : vectorPrincipal h dd a k =
      ∑ l : Idx, h k l*((1/2:ℝ)*∑ p : Idx, ∑ q : Idx,
        h p q*(dd a p q l+dd a q p l-dd a l p q)) := by
    simp only [vectorPrincipal, gammaPrincipal, Fin.sum_univ_three]
    ring
  intro i j
  calc
    liePrincipal g h dd i j =
        (∑ k : Idx, g j k*vectorPrincipal h dd i k)+
        (∑ k : Idx, g i k*vectorPrincipal h dd j k) := by
      simp only [liePrincipal, Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [hg k j]
    _ = (1/2:ℝ)*(∑ p : Idx, ∑ q : Idx,
          h p q*(dd i p q j+dd i q p j-dd i j p q))+
        (1/2:ℝ)*(∑ p : Idx, ∑ q : Idx,
          h p q*(dd j p q i+dd j q p i-dd j i p q)) := by
      simp_rw [hv]
      rw [hc j, hc i]
    _ = ∑ a : Idx, ∑ b : Idx, h a b*
          (dd a i b j+dd a j b i-dd i j a b) := by
      simp only [Fin.sum_univ_three]
      simp only [hh, hcomm]
      ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateDeTurckPrincipal
