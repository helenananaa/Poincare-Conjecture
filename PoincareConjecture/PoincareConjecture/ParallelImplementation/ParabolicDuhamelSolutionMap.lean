import PoincareConjecture.ParallelImplementation.ClampedDuhamelValueLinear
import PoincareConjecture.ParallelImplementation.BoundedLinearLift
import PoincareConjecture.ParallelImplementation.FullSlabSolutionWitness
import PoincareConjecture.ParallelImplementation.FullVectorDuhamelJet
import PoincareConjecture.ParallelImplementation.FullJetValueExtensionality
import PoincareConjecture.ParallelImplementation.SlabClampLinearExtension
import PoincareConjecture.ParallelImplementation.FullParabolicJetSubmodule
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.VectorDuhamelBoundedLinear
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ParabolicDuhamelSolutionMap
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open MorganTianLib.ParabolicPDE Set MeasureTheory
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
/-- Construct the bounded linear map from genuine forcing jets to complete solution jets. -/
theorem exists_parabolic_duhamel_solution_map (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ 1 →
      ∀ (X : Submodule ℝ (ForcingJet E6 T)) (Y : Submodule ℝ (FullJet T)),
        (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha →
        (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le →
        ∃ D : X →L[ℝ] Y, ‖D‖ ≤ C ∧ ∀ F : X,
          let z : FullJet T := (D F).1
          (∀ (p : Slab T) (k : Fin 6), (z.1.1.1.1 p) k =
            ∫ s in (0:ℝ)..(p.1:ℝ), ∫ y : E3,
              euclideanHeatKernel 3 ((p.1:ℝ)-s) (p.2-y) *
                ((F.1.1 (Set.projIcc 0 T hT.le s,y)) k)) ∧
          ∀ p : Slab T, z.1.2 p - ∑ i : Fin 3,
            z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = F.1.1 p :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, hW⟩ :=
    PoincareConjecture.ParallelImplementation.FullSlabSolutionWitness.exists_full_slab_solution_witness alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro T hT hT1 X Y hX hY
  let Q : Y →ₗ[ℝ] (Slab T →ᵇ E6) :=
    { toFun := fun z => z.1.1.1.1.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hQ : Function.Injective Q := by
    intro z w h
    apply Subtype.ext
    exact PoincareConjecture.ParallelImplementation.FullJetValueExtensionality.full_jet_eq_of_value_eq
      T alpha hT z.1 w.1 (hY ▸ z.2) (hY ▸ w.2) h
  obtain ⟨v0, hv0⟩ :=
    PoincareConjecture.ParallelImplementation.ClampedDuhamelValueLinear.exists_clamped_duhamel_value_linear T hT.le
  let v : X →ₗ[ℝ] (Slab T →ᵇ E6) :=
    { toFun := fun F => v0 F.1.1
      map_add' := fun F G => v0.map_add F.1.1 G.1.1
      map_smul' := fun a F => v0.map_smul a F.1.1 }
  have hfamily := fun F : X => hW T hT hT1 F.1 (hX ▸ F.2)
  choose z hz hn hv hr using hfamily
  have hzY (F : X) : z F ∈ (Y : Set (FullJet T)) := by
    rw [hY]
    exact hz F
  let w (F : X) : Y := ⟨z F, hzY F⟩
  have hwQ (F : X) : Q (w F) = v F := by
    apply BoundedContinuousFunction.ext
    intro p
    ext k
    change (z F).1.1.1.1 p k = v0 F.1.1 p k
    exact (hv F p k).trans (hv0 F.1.1 p k).symm
  have hlift : ∀ F : X, ∃ y : Y, Q y = v F ∧ ‖y‖ ≤ C * ‖F‖ := by
    intro F
    exact ⟨w F, hwQ F, hn F⟩
  obtain ⟨D, hD, hDQ⟩ :=
    PoincareConjecture.ParallelImplementation.BoundedLinearLift.exists_bounded_linear_lift
      Q hQ v C hC.le hlift
  refine ⟨D, hD, ?_⟩
  intro F
  have heq : D F = w F := hQ ((hDQ F).trans (hwQ F).symm)
  rw [heq]
  exact ⟨hv F, hr F⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ParabolicDuhamelSolutionMap
