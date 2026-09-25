import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixPrincipalCoordinateIdentity
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem six_principal_coordinate_identity
    (H : E3 →L[ℝ] E3 →L[ℝ] E6) (b : E3 →L[ℝ] E3) :

    ∀ i j : Idx,
      symmetricSixMatrix ((∑ a : Idx, H (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)) +
        (∑ a : Idx, ∑ c : Idx, ((b-1) (EuclideanSpace.single c 1)) a •
          H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1))) i j =
        ∑ a : Idx, ∑ c : Idx, (b (EuclideanSpace.single c 1)) a *
          symmetricSixMatrix (H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro i j
  have hcontract (f g : Idx → Idx → ℝ) :
      (∑ c : Idx, f c c) +
          ∑ a : Idx, ∑ c : Idx, (g a c - (if a = c then 1 else 0)) * f a c =
        ∑ a : Idx, ∑ c : Idx, g a c * f a c := by
    simp [Fin.sum_univ_succ, sub_mul]
  fin_cases i <;> fin_cases j <;>
    simp only [symmetricSixMatrix] <;>
    exact hcontract
      (fun a c => ((H (EuclideanSpace.single a 1))
        (EuclideanSpace.single c 1)).ofLp _)
      (fun a c => (b (EuclideanSpace.single c 1)).ofLp a)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixPrincipalCoordinateIdentity
