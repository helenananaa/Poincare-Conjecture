import PoincareConjecture.ParallelImplementation.ParabolicDuhamelSolutionMap
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ParabolicDuhamelResidual
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open scoped BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance (T : ℝ) : NormedAddCommGroup (FullJet T) := inferInstance
local instance (T : ℝ) : NormedSpace ℝ (FullJet T) := inferInstance
local instance (T : ℝ) : NormedAddCommGroup (ForcingJet E6 T) := inferInstance
local instance (T : ℝ) : NormedSpace ℝ (ForcingJet E6 T) := inferInstance
local instance (T : ℝ) (S : Submodule ℝ (FullJet T)) : NormedAddCommGroup S := inferInstance
local instance (T : ℝ) (S : Submodule ℝ (FullJet T)) : NormedSpace ℝ S := inferInstance
local instance (T : ℝ) (S : Submodule ℝ (ForcingJet E6 T)) : NormedAddCommGroup S := inferInstance
local instance (T : ℝ) (S : Submodule ℝ (ForcingJet E6 T)) : NormedSpace ℝ S := inferInstance
theorem exists_parabolic_duhamel_residual (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ 1 →
      ∀ (X : Submodule ℝ (ForcingJet E6 T)) (Y : Submodule ℝ (FullJet T)),
        (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha →
        (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le →
        ∃ D : X →L[ℝ] Y, ‖D‖ ≤ C ∧ ∀ F : X, ∀ p : Slab T,
          (D F).1.1.2 p - ∑ i : Fin 3,
            (D F).1.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = F.1.1 p :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hC, hMap⟩ :=
    PoincareConjecture.ParallelImplementation.ParabolicDuhamelSolutionMap.exists_parabolic_duhamel_solution_map
      alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro T hT hT1 X Y hX hY
  obtain ⟨D, hD, hFacts⟩ := hMap T hT hT1 X Y hX hY
  refine ⟨D, hD, ?_⟩
  intro F p
  exact (hFacts F).2 p
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ParabolicDuhamelResidual
