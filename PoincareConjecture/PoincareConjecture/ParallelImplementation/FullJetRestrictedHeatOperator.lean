import PoincareConjecture.ParallelImplementation.FullJetHeatOperator
import PoincareConjecture.ParallelImplementation.BoundedSubmoduleRestriction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullJetRestrictedHeatOperator
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
theorem exists_full_jet_restricted_heat_operator
    (T alpha : ℝ) (hT : 0 ≤ T)
    (X : Submodule ℝ (ForcingJet E6 T)) (Y : Submodule ℝ (FullJet T))
    (hX : (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha)
    (hY : (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT) :
    ∃ L : Y →L[ℝ] X, ‖L‖ ≤ 4 ∧ ∀ z : Y, ∀ p : Slab T,
      (L z).1.1 p = z.1.1.2 p - ∑ i : Fin 3,
        z.1.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨A, hA_norm, hA_formula, hA_invariant, hA_map⟩ :=
    PoincareConjecture.ParallelImplementation.FullJetHeatOperator.exists_full_jet_heat_operator
      T alpha hT
  have hmap (z : FullJet T) (hz : z ∈ Y) : A z ∈ X := by
    have hz' : z ∈ fullParabolicJetSet T alpha hT := hY ▸ hz
    have hAz : A z ∈ forcingGraph E6 T alpha := hA_map z hz'
    have hmem : (A z ∈ (X : Set (ForcingJet E6 T))) =
        (A z ∈ forcingGraph E6 T alpha) :=
      congrArg (fun S : Set (ForcingJet E6 T) => A z ∈ S) hX
    exact hmem.symm ▸ hAz
  obtain ⟨L, hL_norm, hL_apply⟩ :=
    PoincareConjecture.ParallelImplementation.BoundedSubmoduleRestriction.exists_bounded_submodule_restriction
      A Y X hmap
  refine ⟨L, hL_norm.trans hA_norm, ?_⟩
  intro z p
  have hLz := hL_apply z
  calc
    (L z).1.1 p = (A (z : FullJet T)).1 p := by
      exact congrArg (fun q : ForcingJet E6 T => q.1 p) hLz
    _ = (z : FullJet T).1.2 p - ∑ i : Fin 3,
        (z : FullJet T).1.1.1.2.2 p
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := hA_formula _ _
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullJetRestrictedHeatOperator
