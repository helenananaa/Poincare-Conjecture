import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateOperatorEntries
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_operator_entries :

    ∃ C : (E3 →L[ℝ] E3) →L[ℝ] Mat, ‖C‖ ≤ 1 ∧ Function.Injective C ∧
      (∀ (A : E3 →L[ℝ] E3) (i j : Idx), C A i j = (A (EuclideanSpace.single j 1)) i) ∧
      C 1 = (fun i j => if i = j then 1 else 0) ∧
      ∀ (A B : E3 →L[ℝ] E3) (i j : Idx), C (A * B) i j = ∑ k : Idx, C A i k * C B k j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let L : (E3 →L[ℝ] E3) →ₗ[ℝ] Mat :=
    { toFun := fun A i j => (A (EuclideanSpace.single j 1)) i
      map_add' := by
        intro A B
        funext i j
        simp
      map_smul' := by
        intro c A
        funext i j
        simp }
  have hbound (A : E3 →L[ℝ] E3) : ‖L A‖ ≤ ‖A‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro j
    have hcoord :
        ‖(A (EuclideanSpace.single j 1)) i‖ ≤ ‖A (EuclideanSpace.single j 1)‖ := by
      simpa using
        (PiLp.norm_apply_le (p := 2) (x := A (EuclideanSpace.single j 1)) i)
    calc
      ‖(A (EuclideanSpace.single j 1)) i‖ ≤ ‖A (EuclideanSpace.single j 1)‖ := hcoord
      _ ≤ ‖A‖ * ‖EuclideanSpace.single j 1‖ := A.le_opNorm _
      _ = ‖A‖ := by simp
  let C : (E3 →L[ℝ] E3) →L[ℝ] Mat :=
    L.mkContinuous 1 (fun A => by simpa using hbound A)
  have h_expand (v : E3) :
      v = ∑ k : Idx, v k • EuclideanSpace.single k 1 := by
    simpa using ((EuclideanSpace.basisFun Idx ℝ).sum_repr v).symm
  refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [C] using
      (LinearMap.mkContinuous_norm_le L zero_le_one (fun A => by simpa using hbound A))
  · intro A B hAB
    have hcoord (i j : Idx) :
        (A (EuclideanSpace.single j 1)) i = (B (EuclideanSpace.single j 1)) i := by
      have h := congrArg (fun M : Mat => M i j) hAB
      simpa [C, L] using h
    have hbasis (j : Idx) :
        A (EuclideanSpace.single j 1) = B (EuclideanSpace.single j 1) := by
      ext i
      exact hcoord i j
    apply ContinuousLinearMap.ext
    intro x
    calc
      A x = A (∑ j : Idx, x j • EuclideanSpace.single j 1) :=
        congrArg A (h_expand x)
      _ = ∑ j : Idx, x j • A (EuclideanSpace.single j 1) := by simp
      _ = ∑ j : Idx, x j • B (EuclideanSpace.single j 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hbasis]
      _ = B (∑ j : Idx, x j • EuclideanSpace.single j 1) := by simp
      _ = B x := (congrArg B (h_expand x)).symm
  · intro A i j
    rfl
  · ext i j
    simp [C, L]
  · intro A B i j
    change (A (B (EuclideanSpace.single j 1))) i =
      ∑ k : Idx, (A (EuclideanSpace.single k 1)) i * (B (EuclideanSpace.single j 1)) k
    have hB := h_expand (B (EuclideanSpace.single j 1))
    have hAB : A (B (EuclideanSpace.single j 1)) =
        ∑ k : Idx, (B (EuclideanSpace.single j 1)) k • A (EuclideanSpace.single k 1) := by
      calc
        A (B (EuclideanSpace.single j 1)) =
            A (∑ k : Idx, (B (EuclideanSpace.single j 1)) k • EuclideanSpace.single k 1) :=
          congrArg A hB
        _ = ∑ k : Idx, (B (EuclideanSpace.single j 1)) k • A (EuclideanSpace.single k 1) := by
          simp
    have hcoord := congrArg (fun v : E3 => v i) hAB
    simpa [mul_comm] using hcoord
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateOperatorEntries
