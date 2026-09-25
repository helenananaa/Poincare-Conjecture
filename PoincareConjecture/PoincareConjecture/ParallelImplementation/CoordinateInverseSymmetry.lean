import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateInverseSymmetry
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open MorganTianLib.MetricCoefficient
theorem inverse_matrix_symmetric
    (g h : Mat) (hg : ∀ i j : Idx, g i j = g j i)
    (hRight : ∀ i j : Idx, (∑ k : Idx, g i k * h k j) = if i = j then 1 else 0)
    (hLeft : ∀ i j : Idx, (∑ k : Idx, h i k * g k j) = if i = j then 1 else 0) :

    ∀ i j : Idx, h i j = h j i :=
/- SWARM_PROOF_BEGIN -/
by
  let G : Matrix Idx Idx ℝ := g
  let H : Matrix Idx Idx ℝ := h
  have hGsymm : G.transpose = G := by
    ext i j
    exact hg j i
  have hGH : G * H = 1 := by
    ext i j
    simpa [G, H, Matrix.mul_apply, Matrix.one_apply] using hRight i j
  have hHTG : H.transpose * G = 1 := by
    have htranspose : (G * H).transpose = (1 : Matrix Idx Idx ℝ) := by
      rw [hGH]
      simp
    rw [Matrix.transpose_mul, hGsymm] at htranspose
    exact htranspose
  have htranspose_eq : H.transpose = H := by
    calc
      H.transpose = H.transpose * 1 := by simp
      _ = H.transpose * (G * H) := by rw [hGH]
      _ = (H.transpose * G) * H := by rw [Matrix.mul_assoc]
      _ = 1 * H := by rw [hHTG]
      _ = H := by simp
  intro i j
  have hentry := congrArg (fun M : Matrix Idx Idx ℝ => M i j) htranspose_eq
  simpa using hentry.symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateInverseSymmetry
