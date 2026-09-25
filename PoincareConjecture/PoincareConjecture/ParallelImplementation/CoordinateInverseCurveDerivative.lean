import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateInverseCurveDerivative
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem inverse_derivative_formula
    (g h : ℝ → Mat) (dg dh : Mat) (t : ℝ)
    (hg : ∀ i j, HasDerivAt (fun r => g r i j) (dg i j) t)
    (hh : ∀ i j, HasDerivAt (fun r => h r i j) (dh i j) t)
    (hInv : ∀ᶠ r in 𝓝 t, ∀ i j : Idx, (∑ k : Idx, g r i k * h r k j) = if i = j then 1 else 0)
    (hLeft : ∀ i j : Idx, (∑ k : Idx, h t i k * g t k j) = if i = j then 1 else 0) :

    ∀ i j : Idx, dh i j = -(∑ r : Idx, ∑ s : Idx, h t i r * dg r s * h t s j) :=
/- SWARM_PROOF_BEGIN -/
by
  have hprod_deriv (i j : Idx) :
      HasDerivAt (fun r : ℝ => ∑ k : Idx, g r i k * h r k j)
        (∑ k : Idx, (dg i k * h t k j + g t i k * dh k j)) t := by
    simpa using (HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hg i k).mul (hh k j))
  have hderiv_eq (i j : Idx) :
      (∑ k : Idx, (dg i k * h t k j + g t i k * dh k j)) = 0 := by
    have heq :
        (fun r : ℝ => if i = j then (1 : ℝ) else 0) =ᶠ[𝓝 t]
          (fun r => ∑ k : Idx, g r i k * h r k j) :=
      hInv.mono fun r hr => (hr i j).symm
    have hconst := (hprod_deriv i j).congr_of_eventuallyEq heq
    have hconst' : HasDerivAt (fun _ : ℝ => if i = j then (1 : ℝ) else 0) 0 t :=
      hasDerivAt_const t _
    simpa using hconst.unique hconst'
  have hcollapse (i j : Idx) :
      (∑ r : Idx, ∑ s : Idx, h t i r * g t r s * dh s j) = dh i j := by
    rw [Finset.sum_comm]
    calc
      (∑ s : Idx, ∑ r : Idx, h t i r * g t r s * dh s j) =
          ∑ s : Idx, (∑ r : Idx, h t i r * g t r s) * dh s j := by
        apply Finset.sum_congr rfl
        intro s _
        rw [← Finset.sum_mul]
      _ = ∑ s : Idx, (if i = s then 1 else 0) * dh s j := by
        apply Finset.sum_congr rfl
        intro s _
        rw [hLeft i s]
      _ = dh i j := by simp
  intro i j
  have hweighted :
      (∑ r : Idx, h t i r *
        (∑ s : Idx, (dg r s * h t s j + g t r s * dh s j))) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    simp [hderiv_eq r j]
  have hsplit :
      (∑ r : Idx, h t i r *
        (∑ s : Idx, (dg r s * h t s j + g t r s * dh s j))) =
        (∑ r : Idx, ∑ s : Idx, h t i r * dg r s * h t s j) +
        (∑ r : Idx, ∑ s : Idx, h t i r * g t r s * dh s j) := by
    calc
      (∑ r : Idx, h t i r *
        (∑ s : Idx, (dg r s * h t s j + g t r s * dh s j))) =
          ∑ r : Idx, (h t i r * (∑ s : Idx, dg r s * h t s j) +
            h t i r * (∑ s : Idx, g t r s * dh s j)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_add_distrib, mul_add]
      _ = ∑ r : Idx,
          ((∑ s : Idx, h t i r * dg r s * h t s j) +
            (∑ s : Idx, h t i r * g t r s * dh s j)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro s _ <;> ring
      _ = (∑ r : Idx, ∑ s : Idx, h t i r * dg r s * h t s j) +
          (∑ r : Idx, ∑ s : Idx, h t i r * g t r s * dh s j) := by
        rw [Finset.sum_add_distrib]
  have hsum :
      (∑ r : Idx, ∑ s : Idx, h t i r * dg r s * h t s j) +
        (∑ r : Idx, ∑ s : Idx, h t i r * g t r s * dh s j) = 0 := by
    rw [← hsplit]
    exact hweighted
  rw [hcollapse i j] at hsum
  linarith
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateInverseCurveDerivative
