import PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse
import PoincareConjecture.ParallelImplementation.CoefficientHessianMultiplier
import PoincareConjecture.ParallelImplementation.RightInverseSmallPerturbation
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmallCoefficientParabolicSolver
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
/-- A genuine zero-initial-value solver for a small variable-coefficient perturbation of heat. -/
theorem small_coefficient_parabolic_solver (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ 1 →
      ∀ A : Fin 3 → Fin 3 → ForcingJet ℝ T,
      (∀ i j, A i j ∈ forcingGraph ℝ T alpha) →
      4*C*(∑ i : Fin 3, ∑ j : Fin 3, ‖A i j‖) ≤ 1 →
      ∃ (X : Submodule ℝ (ForcingJet E6 T)) (Y : Submodule ℝ (FullJet T)),
        (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha ∧
        (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le ∧
        CompleteSpace X ∧ CompleteSpace Y ∧
        ∃ D : X →L[ℝ] Y, ‖D‖ ≤ 2*C ∧ ∀ F : X,
          let z : FullJet T := (D F).1
          ∀ p : Slab T,
            z.1.2 p - (∑ i : Fin 3, z.1.1.1.2.2 p
              (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) -
              (∑ i : Fin 3, ∑ j : Fin 3, (A i j).1 p • z.1.1.1.2.2 p
                (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = F.1.1 p :=
/- SWARM_PROOF_BEGIN -/
by
  rcases PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse.exists_parabolic_heat_right_inverse
      alpha ha ha1 with ⟨C, hC, hheat⟩
  refine ⟨C, hC, ?_⟩
  intro T hT hT1 A hA hsmall
  rcases hheat T hT hT1 with
    ⟨X, Y, hX, hY, hXcomplete, hYcomplete, L, D, hLnorm, hDnorm, hLD, hLvalue⟩
  letI : CompleteSpace X := hXcomplete
  letI : CompleteSpace Y := hYcomplete
  obtain ⟨R, hRnorm, hRvalue, _hRincrement, hRmaps⟩ :=
    PoincareConjecture.ParallelImplementation.CoefficientHessianMultiplier.exists_coefficient_hessian_multiplier
      T alpha (le_of_lt hT) A hA
  have hRmap (z : FullJet T) (hz : z ∈ Y) : R z ∈ X := by
    have hz' : z ∈ fullParabolicJetSet T alpha hT.le := hY ▸ hz
    have hRz := hRmaps z hz'
    have hmem : (R z ∈ (X : Set (ForcingJet E6 T))) =
        (R z ∈ forcingGraph E6 T alpha) :=
      congrArg (fun S : Set (ForcingJet E6 T) => R z ∈ S) hX
    exact hmem.symm ▸ hRz
  obtain ⟨R₀, hR₀norm, hR₀value⟩ :=
    PoincareConjecture.ParallelImplementation.BoundedSubmoduleRestriction.exists_bounded_submodule_restriction
      R Y X hRmap
  let RY : Y →L[ℝ] X := R₀
  let s : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ‖A i j‖
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have hRYnorm : ‖RY‖ ≤ 2 * s := by
    calc
      ‖RY‖ = ‖R₀‖ := rfl
      _ ≤ ‖R‖ := hR₀norm
      _ ≤ 2 * s := by simpa [s] using hRnorm
  have hcomp : ‖RY.comp D‖ ≤ 2 * s * C := by
    calc
      ‖RY.comp D‖ ≤ ‖RY‖ * ‖D‖ := RY.opNorm_comp_le D
      _ ≤ (2 * s) * C :=
        mul_le_mul hRYnorm hDnorm (norm_nonneg D) (mul_nonneg (by norm_num) hs)
  have hsmall' : 4 * C * s ≤ 1 := by
    simpa [s] using hsmall
  have hhalf : 2 * s * C ≤ (1 : ℝ) / 2 := by
    nlinarith [hsmall']
  have hcompHalf : ‖RY.comp D‖ ≤ (1 : ℝ) / 2 := hcomp.trans hhalf
  have hcompSmall : ‖RY.comp D‖ < 1 :=
    lt_of_le_of_lt hcompHalf (by norm_num)
  obtain ⟨E, hEright, hEnorm⟩ :=
    PoincareConjecture.ParallelImplementation.RightInverseSmallPerturbation.right_inverse_small_perturbation
      L RY D hLD hcompSmall
  have hden : (1 : ℝ) / 2 ≤ 1 - ‖RY.comp D‖ := by linarith
  have hdenpos : 0 < 1 - ‖RY.comp D‖ := by linarith
  have hEbound : ‖E‖ ≤ 2 * C := by
    calc
      ‖E‖ ≤ ‖D‖ / (1 - ‖RY.comp D‖) := hEnorm
      _ ≤ C / (1 - ‖RY.comp D‖) :=
        div_le_div_of_nonneg_right hDnorm hdenpos.le
      _ ≤ 2 * C := (div_le_iff₀ hdenpos).2 <| by
        calc
          C = (2 * C) * ((1 : ℝ) / 2) := by ring
          _ ≤ (2 * C) * (1 - ‖RY.comp D‖) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
  refine ⟨X, Y, hX, hY, hXcomplete, hYcomplete, E, hEbound, ?_⟩
  intro F
  dsimp
  intro p
  let z : FullJet T := (E F).1
  have hoperator : (L - RY) (E F) = F := by
    have h := congrArg (fun Q : X →L[ℝ] X => Q F) hEright
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  have hvalue : (L (E F)).1.1 p - (RY (E F)).1.1 p = F.1.1 p := by
    have hv := congrArg (fun q : X => (q : ForcingJet E6 T).1.1 p) hoperator
    simpa using hv
  have hLpoint : (L (E F)).1.1 p =
      z.1.2 p - ∑ i : Fin 3,
        z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    simpa [z] using hLvalue (E F) p
  have hRpoint : (RY (E F)).1.1 p =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (A i j).1 p • z.1.1.1.2.2 p
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    calc
      (RY (E F)).1.1 p = (R ((E F : Y) : FullJet T)).1 p := by
        exact congrArg (fun q : ForcingJet E6 T => q.1 p) (hR₀value (E F))
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          (A i j).1 p • z.1.1.1.2.2 p
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
        simpa [z] using hRvalue ((E F : Y) : FullJet T) p
  rw [hLpoint, hRpoint] at hvalue
  exact hvalue
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmallCoefficientParabolicSolver
