import PoincareConjecture.ParallelImplementation.CoefficientHessianMultiplierModular
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoefficientHessianMultiplier
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Actual variable-coefficient Hessian contraction on value and Holder-increment fields. -/
theorem exists_coefficient_hessian_multiplier (T alpha : ℝ) (hT : 0 ≤ T)
    (A : Fin 3 → Fin 3 → ForcingJet ℝ T)
    (hA : ∀ i j, A i j ∈ forcingGraph ℝ T alpha) :
    ∃ R : FullJet T →L[ℝ] ForcingJet E6 T,
      ‖R‖ ≤ 2 * (∑ i : Fin 3, ∑ j : Fin 3, ‖A i j‖) ∧
      (∀ z p, (R z).1 p = ∑ i : Fin 3, ∑ j : Fin 3,
        (A i j).1 p • z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      (∀ z p, (R z).2 p = ∑ i : Fin 3, ∑ j : Fin 3,
        ((A i j).1 p.1.1 • z.1.1.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
         (A i j).2 p • z.1.1.1.2.2 p.1.2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) ∧
      ∀ z ∈ fullParabolicJetSet T alpha hT, R z ∈ forcingGraph E6 T alpha :=
/- SWARM_PROOF_BEGIN -/
by
  exact PoincareConjecture.ParallelImplementation.CoefficientHessianMultiplierModular.exists_coefficient_hessian_multiplier_modular T alpha hT A hA
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoefficientHessianMultiplier