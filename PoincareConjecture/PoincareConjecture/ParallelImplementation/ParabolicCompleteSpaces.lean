import PoincareConjecture.ParallelImplementation.FullParabolicJetSubmodule
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ParabolicCompleteSpaces
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Isolate the two exact complete graph spaces from their larger construction interfaces. -/
theorem exists_complete_parabolic_spaces (T alpha : ℝ) (hT : 0 ≤ T) (ha : 0 < alpha) :
    ∃ (X : Submodule ℝ (ForcingJet E6 T)) (Y : Submodule ℝ (FullJet T)),
      (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha ∧
      (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT ∧
      CompleteSpace X ∧ CompleteSpace Y := by
  obtain ⟨X, hX, hXC, _⟩ := parabolic_forcing_submodule_complete E6 T alpha ha
  obtain ⟨Y, hY, hYC⟩ :=
    PoincareConjecture.ParallelImplementation.FullParabolicJetSubmodule.full_parabolic_jet_submodule T alpha hT ha
  exact ⟨X, Y, hX, hY, hXC, hYC⟩
end PoincareConjecture.ParallelImplementation.ParabolicCompleteSpaces
