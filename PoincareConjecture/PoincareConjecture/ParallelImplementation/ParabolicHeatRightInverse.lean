import PoincareConjecture.ParallelImplementation.ParabolicDuhamelResidual
import PoincareConjecture.ParallelImplementation.FullJetRestrictedHeatOperator
import PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
import PoincareConjecture.ParallelImplementation.BoundedSubmoduleRestriction
import PoincareConjecture.ParallelImplementation.ParabolicCompleteSpaces
import PoincareConjecture.ParallelImplementation.ParabolicDuhamelSolutionMap
import PoincareConjecture.ParallelImplementation.FullJetHeatOperator
import PoincareConjecture.ParallelImplementation.FullParabolicJetSubmodule
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open scoped Topology BigOperators BoundedContinuousFunction
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
/-- A uniformly bounded right inverse for the actual six-component heat operator. -/
theorem exists_parabolic_heat_right_inverse (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ 1 →
      ∃ (X : Submodule ℝ (ForcingJet E6 T)) (Y : Submodule ℝ (FullJet T)),
        (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha ∧
        (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le ∧
        CompleteSpace X ∧ CompleteSpace Y ∧
        ∃ (L : Y →L[ℝ] X) (D : X →L[ℝ] Y),
          ‖L‖ ≤ 4 ∧ ‖D‖ ≤ C ∧ L.comp D = ContinuousLinearMap.id ℝ X ∧
          ∀ z : Y, let w : FullJet T := z.1
            ∀ p : Slab T, (L z).1.1 p = w.1.2 p - ∑ i : Fin 3,
              w.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) :=
/- SWARM_PROOF_BEGIN -/
by
  rcases PoincareConjecture.ParallelImplementation.ParabolicDuhamelResidual.exists_parabolic_duhamel_residual
      alpha ha ha1 with ⟨C, hC, hD⟩
  refine ⟨C, hC, ?_⟩
  intro T hT hT1
  have hspaces := PoincareConjecture.ParallelImplementation.ParabolicCompleteSpaces.exists_complete_parabolic_spaces
      T alpha hT.le ha
  rcases hspaces with ⟨X, Y, hrest⟩
  rcases hrest with ⟨hX, hY, hcomplete⟩
  rcases hcomplete with ⟨hXcomplete, hYcomplete⟩
  have hLexists := PoincareConjecture.ParallelImplementation.FullJetRestrictedHeatOperator.exists_full_jet_restricted_heat_operator
      T alpha hT.le X Y hX hY
  rcases hLexists with ⟨L, hLrest⟩
  rcases hLrest with ⟨hLnorm, hLvalue⟩
  have hDexists := hD T hT hT1 X Y hX hY
  rcases hDexists with ⟨D, hDrest⟩
  rcases hDrest with ⟨hDnorm, hDvalue⟩
  have hLD : L.comp D = ContinuousLinearMap.id ℝ X := by
    apply ContinuousLinearMap.ext
    intro F
    apply Subtype.ext
    change (L (D F)).1 = F.1
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro p
      exact (hLvalue (D F) p).trans (hDvalue F p)
    · apply BoundedContinuousFunction.ext
      intro p
      have hLgraph : (L (D F)).1 ∈ forcingGraph E6 T alpha := by
        have hmem : (L (D F)).1 ∈ (X : Set (ForcingJet E6 T)) := (L (D F)).2
        exact (congrArg (fun s : Set (ForcingJet E6 T) => (L (D F)).1 ∈ s) hX).mp hmem
      change ∀ q : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T,
        (L (D F)).1.2 q =
          (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho q.1.1 q.1.2 ^ alpha)⁻¹ •
            ((L (D F)).1.1 q.1.1 - (L (D F)).1.1 q.1.2) at hLgraph
      have hFgraph : F.1 ∈ forcingGraph E6 T alpha := by
        have hmem : F.1 ∈ (X : Set (ForcingJet E6 T)) := F.2
        exact (congrArg (fun s : Set (ForcingJet E6 T) => F.1 ∈ s) hX).mp hmem
      change ∀ q : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T,
        F.1.2 q =
          (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho q.1.1 q.1.2 ^ alpha)⁻¹ •
            (F.1.1 q.1.1 - F.1.1 q.1.2) at hFgraph
      calc
        (L (D F)).1.2 p =
            (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
              ((L (D F)).1.1 p.1.1 - (L (D F)).1.1 p.1.2) := hLgraph p
        _ = (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
              (F.1.1 p.1.1 - F.1.1 p.1.2) := by
          apply congrArg (fun v : E6 =>
            (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho
              p.1.1 p.1.2 ^ alpha)⁻¹ • v)
          exact
            (congrArg₂ (fun a b : E6 => a - b)
              (hLvalue (D F) p.1.1) (hLvalue (D F) p.1.2)).trans
              (congrArg₂ (fun a b : E6 => a - b)
                (hDvalue F p.1.1) (hDvalue F p.1.2))
        _ = F.1.2 p := (hFgraph p).symm
  exact ⟨X, Y, hX, hY, hXcomplete, hYcomplete, L, D, hLnorm, hDnorm, hLD, hLvalue⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse
