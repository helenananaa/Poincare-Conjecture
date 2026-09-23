import Mathlib
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.IndependentAlgebra
open scoped BigOperators RealInnerProductSpace
theorem quadratic_bound_of_entry_bound
    {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i j, |A i j| ≤ C) (x : n → ℝ) :
    |∑ i, ∑ j, x i * A i j * x j| ≤
      (Fintype.card n : ℝ) * C * (∑ i, (x i)^2) :=
/- SWARM_PROOF_BEGIN -/
by
  let s : ℝ := ∑ i, |x i|
  have hcs : s ^ 2 ≤ (Fintype.card n : ℝ) * ∑ i, (x i) ^ 2 := by
    dsimp [s]
    calc
      (∑ i, |x i|) ^ 2 ≤ (∑ i, (1 : ℝ) ^ 2) * ∑ i, (|x i|) ^ 2 := by
        simpa using
          (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n)
            (fun _ => (1 : ℝ)) (fun i => |x i|))
      _ = (Fintype.card n : ℝ) * ∑ i, (x i) ^ 2 := by simp
  have hterm (i j : n) :
      |x i * A i j * x j| ≤ C * (|x i| * |x j|) := by
    rw [abs_mul, abs_mul]
    calc
      (|x i| * |A i j|) * |x j| = |A i j| * (|x i| * |x j|) := by ring
      _ ≤ C * (|x i| * |x j|) :=
        mul_le_mul_of_nonneg_right (hA i j)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hprod :
      (∑ p : n × n, |x p.1| * |x p.2|) = s ^ 2 := by
    calc
      (∑ p : n × n, |x p.1| * |x p.2|) =
          ∑ i, ∑ j, |x i| * |x j| :=
        Fintype.sum_prod_type' (fun i j => |x i| * |x j|)
      _ = (∑ i, |x i|) * ∑ j, |x j| :=
        (Fintype.sum_mul_sum (fun i => |x i|) (fun j => |x j|)).symm
      _ = s ^ 2 := by simp [s, pow_two]
  have hflat :
      (∑ i, ∑ j, x i * A i j * x j) =
        ∑ p : n × n, x p.1 * A p.1 p.2 * x p.2 := by
    exact (Fintype.sum_prod_type' (fun i j => x i * A i j * x j)).symm
  rw [hflat]
  calc
    |∑ p : n × n, x p.1 * A p.1 p.2 * x p.2|
        ≤ ∑ p : n × n, |x p.1 * A p.1 p.2 * x p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : n × n, C * (|x p.1| * |x p.2|) :=
      Finset.sum_le_sum fun p _ => hterm p.1 p.2
    _ = C * s ^ 2 := by rw [← Finset.mul_sum, hprod]
    _ ≤ C * ((Fintype.card n : ℝ) * ∑ i, (x i) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs hC
    _ = (Fintype.card n : ℝ) * C * (∑ i, (x i) ^ 2) := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.IndependentAlgebra
