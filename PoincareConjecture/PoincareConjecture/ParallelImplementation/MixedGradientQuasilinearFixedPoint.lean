import PoincareConjecture.ParallelImplementation.MixedProjectedForcingBilinear
import PoincareConjecture.ParallelImplementation.ProjectedForcingQuadratic
import PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.MixedGradientQuasilinearFixedPoint
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
 theorem exists_mixed_gradient_quasilinear_solution
    {Y V W U Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T alpha : ℝ) (X : Submodule ℝ (ForcingJet Z T))
    (hX : (X : Set (ForcingJet Z T)) = forcingGraph Z T alpha)
    (L : Y →L[ℝ] X) (D : X →L[ℝ] Y)
    (hLD : L.comp D = ContinuousLinearMap.id ℝ X)
    (B : V →L[ℝ] W →L[ℝ] Z) (C : U →L[ℝ] U →L[ℝ] Z)
    (P : Y →L[ℝ] ForcingJet V T) (Q : Y →L[ℝ] ForcingJet W T)
    (G : Y →L[ℝ] ForcingJet U T)
    (hP : ∀ z, P z ∈ forcingGraph V T alpha)
    (hQ : ∀ z, Q z ∈ forcingGraph W T alpha)
    (hG : ∀ z, G z ∈ forcingGraph U T alpha)
    (f : X) (R : ℝ) (hR : 0 < R)
    (hself : ‖D‖*(‖f‖+(2*‖B‖*‖P‖*‖Q‖+2*‖C‖*‖G‖^2)*R^2) ≤ R)
    (hcontract : 2*‖D‖*(2*‖B‖*‖P‖*‖Q‖+2*‖C‖*‖G‖^2)*R < 1) :
    ∃ z : Y, ‖z‖ ≤ R ∧ ∀ p : Slab T,
      (L z).1.1 p = f.1.1 p + B ((P z).1 p) ((Q z).1 p) +
        C ((G z).1 p) ((G z).1 p) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨N₁, hN₁_zero, hN₁_value, hN₁_lip⟩ :=
    PoincareConjecture.ParallelImplementation.MixedProjectedForcingBilinear.exists_mixed_projected_forcing_bilinear
      T alpha B X hX P Q hP hQ
  obtain ⟨N₂, hN₂_zero, hN₂_value, hN₂_lip⟩ :=
    PoincareConjecture.ParallelImplementation.ProjectedForcingQuadratic.exists_projected_forcing_quadratic
      T alpha C X hX G hG
  let K : ℝ := 2 * ‖B‖ * ‖P‖ * ‖Q‖ + 2 * ‖C‖ * ‖G‖ ^ 2
  let N : Y → X := fun z => N₁ z + N₂ z
  have hN_zero : N 0 = 0 := by
    simp [N, hN₁_zero, hN₂_zero]
  have hN_value (z : Y) (p : Slab T) :
      (N z).1.1 p = B ((P z).1 p) ((Q z).1 p) +
        C ((G z).1 p) ((G z).1 p) := by
    simp [N, hN₁_value, hN₂_value]
  have hN_lip (z w : Y) :
      ‖N z - N w‖ ≤ K * (‖z‖ + ‖w‖) * ‖z - w‖ := by
    have hsum :
        ‖N₁ z - N₁ w‖ + ‖N₂ z - N₂ w‖ ≤
          (2 * ‖B‖ * ‖P‖ * ‖Q‖) * (‖z‖ + ‖w‖) * ‖z - w‖ +
            (2 * ‖C‖ * ‖G‖ ^ 2) * (‖z‖ + ‖w‖) * ‖z - w‖ :=
      add_le_add (hN₁_lip z w) (hN₂_lip z w)
    calc
      ‖N z - N w‖ = ‖(N₁ z - N₁ w) + (N₂ z - N₂ w)‖ := by
        congr 1
        apply Subtype.ext
        change ((N₁ z).1 + (N₂ z).1) - ((N₁ w).1 + (N₂ w).1) =
          ((N₁ z).1 - (N₁ w).1) + ((N₂ z).1 - (N₂ w).1)
        abel
      _ ≤ ‖N₁ z - N₁ w‖ + ‖N₂ z - N₂ w‖ := norm_add_le _ _
      _ ≤ (2 * ‖B‖ * ‖P‖ * ‖Q‖) * (‖z‖ + ‖w‖) * ‖z - w‖ +
            (2 * ‖C‖ * ‖G‖ ^ 2) * (‖z‖ + ‖w‖) * ‖z - w‖ := hsum
      _ = K * (‖z‖ + ‖w‖) * ‖z - w‖ := by
        dsimp [K]
        ring
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  obtain ⟨z, hz, _, hLz, _⟩ :=
    PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint.quadratic_right_inverse_fixed_point
      L D hLD N hN_zero f K R hK hR
      (by intro z w _ _; exact hN_lip z w)
      (by simpa [K] using hself)
      (by simpa [K] using hcontract)
  refine ⟨z, hz, ?_⟩
  intro p
  have hp := congrArg (fun x : X => x.1.1 p) hLz
  simpa [N, hN₁_value, hN₂_value, add_assoc] using hp
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.MixedGradientQuasilinearFixedPoint
