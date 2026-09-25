import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification
import PoincareConjecture.ParallelImplementation.CoordinateOperatorEntries
import PoincareConjecture.ParallelImplementation.CoordinateInverseSymmetry
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixInverseCoordinateAlgebra
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem six_inverse_coordinate_algebra
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j * v j)
    (q : E6) (b : E3 →L[ℝ] E3) (hab : (1+E q)*b=1) (hba : b*(1+E q)=1) :

    let g : Mat := fun i j => (if i=j then 1 else 0)+symmetricSixMatrix q i j
    let h : Mat := fun i j => (b (EuclideanSpace.single j 1)) i
    (∀ i j : Idx, g i j=g j i) ∧ (∀ i j : Idx, h i j=h j i) ∧
    (∀ i j : Idx, (∑ k : Idx, g i k*h k j)=if i=j then 1 else 0) ∧
    (∀ i j : Idx, (∑ k : Idx, h i k*g k j)=if i=j then 1 else 0) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp only
  rcases PoincareConjecture.ParallelImplementation.CoordinateOperatorEntries.exists_operator_entries with
    ⟨C, hC_norm, hC_injective, hC_entries, hC_one, hC_mul⟩
  let g : Mat := fun i j => (if i = j then 1 else 0) + symmetricSixMatrix q i j
  let h : Mat := fun i j => (b (EuclideanSpace.single j 1)) i
  have hEb (i j : Idx) :
      (E q (EuclideanSpace.single j 1)) i = symmetricSixMatrix q i j := by
    simpa [PiLp.single_apply] using hE q (EuclideanSpace.single j 1) i
  have hmetric_basis (i j : Idx) :
      ((1 + E q) (EuclideanSpace.single j 1)) i = g i j := by
    change (EuclideanSpace.single j (1 : ℝ) + E q (EuclideanSpace.single j 1)) i = _
    change (EuclideanSpace.single j (1 : ℝ)) i + (E q (EuclideanSpace.single j 1)) i = _
    rw [PiLp.single_apply, hEb]
  have hCg (i j : Idx) : C (1 + E q) i j = g i j := by
    rw [hC_entries]
    exact hmetric_basis i j
  have hCh (i j : Idx) : C b i j = h i j := by
    rw [hC_entries]
  have hg (i j : Idx) : g i j = g j i := by
    fin_cases i <;> fin_cases j <;> simp [g, symmetricSixMatrix]
  have hRight (i j : Idx) :
      (∑ k : Idx, g i k * h k j) = if i = j then 1 else 0 := by
    calc
      (∑ k : Idx, g i k * h k j) =
          ∑ k : Idx, C (1 + E q) i k * C b k j := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← hCg, ← hCh]
      _ = C ((1 + E q) * b) i j := (hC_mul (1 + E q) b i j).symm
      _ = C 1 i j := congrArg (fun A : E3 →L[ℝ] E3 => C A i j) hab
      _ = if i = j then 1 else 0 := by rw [hC_one]
  have hLeft (i j : Idx) :
      (∑ k : Idx, h i k * g k j) = if i = j then 1 else 0 := by
    calc
      (∑ k : Idx, h i k * g k j) =
          ∑ k : Idx, C b i k * C (1 + E q) k j := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← hCh, ← hCg]
      _ = C (b * (1 + E q)) i j := (hC_mul b (1 + E q) i j).symm
      _ = C 1 i j := congrArg (fun A : E3 →L[ℝ] E3 => C A i j) hba
      _ = if i = j then 1 else 0 := by rw [hC_one]
  have hh : ∀ i j : Idx, h i j = h j i :=
    PoincareConjecture.ParallelImplementation.CoordinateInverseSymmetry.inverse_matrix_symmetric
      g h hg hRight hLeft
  exact ⟨hg, hh, hRight, hLeft⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixInverseCoordinateAlgebra
