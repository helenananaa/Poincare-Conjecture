import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixActualHessianSymmetry
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem actual_six_hessian_symmetry
    (u : E3 → E6) (x : E3) (hu : ContDiffAt ℝ 2 u x) :

    (∀ v w : E3, fderiv ℝ (fderiv ℝ u) x v w = fderiv ℝ (fderiv ℝ u) x w v) ∧
      ∀ a b i j : Idx,
        symmetricSixMatrix (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) i j =
        symmetricSixMatrix (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single b 1) (EuclideanSpace.single a 1)) j i :=
/- SWARM_PROOF_BEGIN -/
by
  have hsym : IsSymmSndFDerivAt ℝ u x :=
    hu.isSymmSndFDerivAt (by simp)
  constructor
  · exact hsym
  · intro a b i j
    rw [hsym]
    fin_cases i <;> fin_cases j <;> simp [symmetricSixMatrix]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixActualHessianSymmetry
