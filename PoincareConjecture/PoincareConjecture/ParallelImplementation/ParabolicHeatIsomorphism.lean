import PoincareConjecture.ParallelImplementation.BoundedClassicalHeatUniqueness
import PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ParabolicHeatIsomorphism
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
/-- Two-sided inversion and a priori bound for the actual zero-trace heat operator. -/
theorem exists_parabolic_heat_isomorphism (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ 1 →
      ∃ (X : Submodule ℝ (ForcingJet E6 T)) (Y : Submodule ℝ (FullJet T)),
        (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha ∧
        (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le ∧
        CompleteSpace X ∧ CompleteSpace Y ∧
        ∃ (L : Y →L[ℝ] X) (D : X →L[ℝ] Y),
          ‖L‖ ≤ 4 ∧ ‖D‖ ≤ C ∧ L.comp D = ContinuousLinearMap.id ℝ X ∧
          D.comp L = ContinuousLinearMap.id ℝ Y ∧
          (∀ z : Y, ‖z‖ ≤ C * ‖L z‖) ∧
          ∀ z : Y, let w : FullJet T := z.1
            ∀ p : Slab T, (L z).1.1 p = w.1.2 p - ∑ i : Fin 3,
              w.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hC, hRight⟩ :=
    PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse.exists_parabolic_heat_right_inverse
      alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro T hT hT1
  rcases hRight T hT hT1 with
    ⟨X, Y, hX, hY, hXcomplete, hYcomplete, L, D,
      hLnorm, hDnorm, hLD, hLvalue⟩
  have hzero (z : Y) (hzL : L z = 0) : z = 0 := by
    apply Subtype.ext
    let w : FullJet T := z.1
    have hmem : w ∈ fullParabolicJetSet T alpha hT.le := by
      have : w ∈ (Y : Set (FullJet T)) := z.2
      rw [hY] at this
      exact this
    have hheat (p : Slab T) : w.1.2 p = ∑ i : Fin 3,
        w.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
      have hformula := hLvalue z p
      have hzval : (L z).1.1 p = 0 := by rw [hzL]; simp
      rw [hzval] at hformula
      exact sub_eq_zero.mp hformula.symm
    exact PoincareConjecture.ParallelImplementation.BoundedClassicalHeatUniqueness.zero_initial_heat_jet_eq_zero
      T alpha hT w hmem hheat
  have hLinj : Function.Injective L := by
    intro z w h
    have hsub : L (z - w) = 0 := by rw [map_sub, h, sub_self]
    have hzero' := hzero (z - w) hsub
    have hval : z.1 - w.1 = 0 := congrArg Subtype.val hzero'
    exact Subtype.ext (sub_eq_zero.mp hval)
  have hDL : D.comp L = ContinuousLinearMap.id ℝ Y := by
    apply ContinuousLinearMap.ext
    intro z
    apply hLinj
    have h := congrArg (fun f : X →L[ℝ] X => f (L z)) hLD
    simpa using h
  have hbound : ∀ z : Y, ‖z‖ ≤ C * ‖L z‖ := by
    intro z
    have hLD_apply := congrArg (fun f : X →L[ℝ] X => f (L z)) hLD
    have hz : D (L z) = z := hLinj (by simpa using hLD_apply)
    calc
      ‖z‖ = ‖D (L z)‖ := by rw [hz]
      _ ≤ ‖D‖ * ‖L z‖ := D.le_opNorm _
      _ ≤ C * ‖L z‖ := mul_le_mul_of_nonneg_right hDnorm (norm_nonneg _)
  exact ⟨X, Y, hX, hY, hXcomplete, hYcomplete, L, D,
    hLnorm, hDnorm, hLD, hDL, hbound, hLvalue⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ParabolicHeatIsomorphism
