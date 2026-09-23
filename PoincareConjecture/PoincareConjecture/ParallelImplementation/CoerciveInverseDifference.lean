import PoincareConjecture.ParallelImplementation.CoerciveInverseEntries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoerciveInverseDifference
open scoped BigOperators RealInnerProductSpace
theorem inverse_entry_difference_le_of_coercive
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : IsUnit A) (hB : IsUnit B)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 < b) (hε : 0 ≤ ε)
    (hAlower : ∀ v : EuclideanSpace ℝ n,
      a * ‖v‖^2 ≤ inner ℝ ((Matrix.toEuclideanLin A).toContinuousLinearMap v) v)
    (hBlower : ∀ v : EuclideanSpace ℝ n,
      b * ‖v‖^2 ≤ inner ℝ ((Matrix.toEuclideanLin B).toContinuousLinearMap v) v)
    (hAB : ∀ i j, |A i j - B i j| ≤ ε) :
    ∀ i j, |A⁻¹ i j - B⁻¹ i j| ≤
      (Fintype.card n : ℝ)^2 * a⁻¹ * ε * b⁻¹ :=
/- SWARM_PROOF_BEGIN -/
by
  intro i j
  have hAinv := PoincareConjecture.ParallelImplementation.IndependentAlgebra.inverse_entry_abs_le_of_coercive
    A hA a ha hAlower
  have hBinv := PoincareConjecture.ParallelImplementation.IndependentAlgebra.inverse_entry_abs_le_of_coercive
    B hB b hb hBlower
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hBmul : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBdet
  have hAmul : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAdet
  have hBcancel : A⁻¹ * B * B⁻¹ = A⁻¹ := by
    calc
      A⁻¹ * B * B⁻¹ = A⁻¹ * (B * B⁻¹) := by rw [mul_assoc]
      _ = A⁻¹ := by rw [hBmul, mul_one]
  have hinvDiff : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
    calc
      A⁻¹ - B⁻¹ = A⁻¹ * B * B⁻¹ - A⁻¹ * A * B⁻¹ := by
        rw [hBcancel, hAmul, one_mul]
      _ = A⁻¹ * (B - A) * B⁻¹ := by noncomm_ring
  have hentry : A⁻¹ i j - B⁻¹ i j = (A⁻¹ * (B - A) * B⁻¹) i j := by
    have h := congrArg (fun M : Matrix n n ℝ => M i j) hinvDiff
    simpa using h
  have hterm (k l : n) :
      |A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| ≤ a⁻¹ * ε * b⁻¹ := by
    have hmid : |B l k - A l k| ≤ ε := by
      simpa only [abs_sub_comm] using hAB l k
    calc
      |A⁻¹ i l * (B l k - A l k) * B⁻¹ k j|
          = (|A⁻¹ i l| * |B l k - A l k|) * |B⁻¹ k j| := by
            simp only [abs_mul]
      _ ≤ (a⁻¹ * ε) * |B⁻¹ k j| := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul (hAinv i l) hmid (abs_nonneg _)
            (inv_nonneg.mpr (le_of_lt ha))
        · exact abs_nonneg _
      _ ≤ (a⁻¹ * ε) * b⁻¹ := by
        apply mul_le_mul_of_nonneg_left (hBinv k j)
        exact mul_nonneg (inv_nonneg.mpr (le_of_lt ha)) hε
      _ = a⁻¹ * ε * b⁻¹ := by ring
  have hsum (k : n) :
      |(∑ l, A⁻¹ i l * (B l k - A l k)) * B⁻¹ k j| ≤
        ∑ l : n, (a⁻¹ * ε * b⁻¹) := by
    calc
      |(∑ l, A⁻¹ i l * (B l k - A l k)) * B⁻¹ k j|
          = |∑ l, A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
            rw [← Finset.sum_mul]
      _ ≤ ∑ l, |A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l : n, (a⁻¹ * ε * b⁻¹) :=
        Finset.sum_le_sum fun l _ => hterm k l
  calc
    |A⁻¹ i j - B⁻¹ i j| =
        |∑ k, (∑ l, A⁻¹ i l * (B l k - A l k)) * B⁻¹ k j| := by
          rw [hentry]
          simp only [Matrix.mul_apply, Matrix.sub_apply]
    _ ≤ ∑ k,
        |(∑ l, A⁻¹ i l * (B l k - A l k)) * B⁻¹ k j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : n, ∑ l : n, (a⁻¹ * ε * b⁻¹) :=
      Finset.sum_le_sum fun k _ => hsum k
    _ = (Fintype.card n : ℝ)^2 * a⁻¹ * ε * b⁻¹ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoerciveInverseDifference
