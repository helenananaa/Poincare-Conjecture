import PoincareConjecture.ParallelImplementation.ProjectedFullInverseBall
import PoincareConjecture.ParallelImplementation.ForcingGraphQuadrilinearLift
import PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.AffineQuadrilinearEstimate
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
theorem affine_quadrilinear_lipschitz
    {Y A V Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (B : A →L[ℝ] A →L[ℝ] V →L[ℝ] V →L[ℝ] Z)
    (I : Y → A) (Q : Y →L[ℝ] V) (v0 : V) (M K R : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 < R)
    (hI : ∀ z : Y, ‖z‖ ≤ R → ‖I z‖ ≤ M)
    (hLip : ∀ z w : Y, ‖z‖ ≤ R → ‖w‖ ≤ R → ‖I z-I w‖ ≤ K*‖z-w‖) :

    let S : ℝ := ‖v0‖+‖Q‖*R
    ∀ z w : Y, ‖z‖ ≤ R → ‖w‖ ≤ R →
      ‖B (I z) (I z) (v0+Q z) (v0+Q z)-B (I w) (I w) (v0+Q w) (v0+Q w)‖ ≤
        ‖B‖*(2*M*K*S^2+2*M^2*‖Q‖*S)*‖z-w‖ :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp only
  intro z w hz hw
  let S : ℝ := ‖v0‖ + ‖Q‖ * R
  have hB (a b : A) (c d : V) :
      ‖B a b c d‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by
    calc
      ‖B a b c d‖ ≤ ‖B a b c‖ * ‖d‖ := (B a b c).le_opNorm d
      _ ≤ (‖B a b‖ * ‖c‖) * ‖d‖ := by
        gcongr
        exact (B a b).le_opNorm c
      _ ≤ ((‖B a‖ * ‖b‖) * ‖c‖) * ‖d‖ := by
        gcongr
        exact (B a).le_opNorm b
      _ ≤ (((‖B‖ * ‖a‖) * ‖b‖) * ‖c‖) * ‖d‖ := by
        gcongr
        exact B.le_opNorm a
  have hIz : ‖I z‖ ≤ M := hI z hz
  have hIw : ‖I w‖ ≤ M := hI w hw
  have hIzw : ‖I z - I w‖ ≤ K * ‖z - w‖ := hLip z w hz hw
  have hPz : ‖v0 + Q z‖ ≤ S := by
    dsimp [S]
    calc
      ‖v0 + Q z‖ ≤ ‖v0‖ + ‖Q z‖ := norm_add_le _ _
      _ ≤ ‖v0‖ + ‖Q‖ * R := by
        gcongr
        calc
          ‖Q z‖ ≤ ‖Q‖ * ‖z‖ := Q.le_opNorm z
          _ ≤ ‖Q‖ * R := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
  have hPw : ‖v0 + Q w‖ ≤ S := by
    dsimp [S]
    calc
      ‖v0 + Q w‖ ≤ ‖v0‖ + ‖Q w‖ := norm_add_le _ _
      _ ≤ ‖v0‖ + ‖Q‖ * R := by
        gcongr
        calc
          ‖Q w‖ ≤ ‖Q‖ * ‖w‖ := Q.le_opNorm w
          _ ≤ ‖Q‖ * R := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
  have hPdiff :
      ‖(v0 + Q z) - (v0 + Q w)‖ ≤ ‖Q‖ * ‖z - w‖ := by
    rw [show (v0 + Q z) - (v0 + Q w) = Q (z - w) by
      rw [map_sub]
      abel]
    exact Q.le_opNorm (z - w)

  have he1 :
      B (I z) (I z) (v0 + Q z) (v0 + Q z) -
          B (I w) (I z) (v0 + Q z) (v0 + Q z) =
        B (I z - I w) (I z) (v0 + Q z) (v0 + Q z) := by
    rw [map_sub]
    rfl
  have he2 :
      B (I w) (I z) (v0 + Q z) (v0 + Q z) -
          B (I w) (I w) (v0 + Q z) (v0 + Q z) =
        B (I w) (I z - I w) (v0 + Q z) (v0 + Q z) := by
    rw [map_sub]
    rfl
  have he3 :
      B (I w) (I w) (v0 + Q z) (v0 + Q z) -
          B (I w) (I w) (v0 + Q w) (v0 + Q z) =
        B (I w) (I w) ((v0 + Q z) - (v0 + Q w)) (v0 + Q z) := by
    rw [map_sub]
    rfl
  have he4 :
      B (I w) (I w) (v0 + Q w) (v0 + Q z) -
          B (I w) (I w) (v0 + Q w) (v0 + Q w) =
        B (I w) (I w) (v0 + Q w) ((v0 + Q z) - (v0 + Q w)) := by
    rw [map_sub]

  let e1 := B (I z) (I z) (v0 + Q z) (v0 + Q z) -
    B (I w) (I z) (v0 + Q z) (v0 + Q z)
  let e2 := B (I w) (I z) (v0 + Q z) (v0 + Q z) -
    B (I w) (I w) (v0 + Q z) (v0 + Q z)
  let e3 := B (I w) (I w) (v0 + Q z) (v0 + Q z) -
    B (I w) (I w) (v0 + Q w) (v0 + Q z)
  let e4 := B (I w) (I w) (v0 + Q w) (v0 + Q z) -
    B (I w) (I w) (v0 + Q w) (v0 + Q w)
  have he1bound : ‖e1‖ ≤ ‖B‖ * (M * K * S ^ 2) * ‖z - w‖ := by
    dsimp [e1]
    rw [he1]
    calc
      ‖B (I z - I w) (I z) (v0 + Q z) (v0 + Q z)‖ ≤
          ‖B‖ * ‖I z - I w‖ * ‖I z‖ * ‖v0 + Q z‖ * ‖v0 + Q z‖ :=
        hB _ _ _ _
      _ ≤ ‖B‖ * (K * ‖z - w‖) * M * S * S := by
        gcongr
      _ = ‖B‖ * (M * K * S ^ 2) * ‖z - w‖ := by ring
  have he2bound : ‖e2‖ ≤ ‖B‖ * (M * K * S ^ 2) * ‖z - w‖ := by
    dsimp [e2]
    rw [he2]
    calc
      ‖B (I w) (I z - I w) (v0 + Q z) (v0 + Q z)‖ ≤
          ‖B‖ * ‖I w‖ * ‖I z - I w‖ * ‖v0 + Q z‖ * ‖v0 + Q z‖ :=
        hB _ _ _ _
      _ ≤ ‖B‖ * M * (K * ‖z - w‖) * S * S := by
        gcongr
      _ = ‖B‖ * (M * K * S ^ 2) * ‖z - w‖ := by ring
  have he3bound :
      ‖e3‖ ≤ ‖B‖ * (M ^ 2 * ‖Q‖ * S) * ‖z - w‖ := by
    dsimp [e3]
    rw [he3]
    calc
      ‖B (I w) (I w) ((v0 + Q z) - (v0 + Q w)) (v0 + Q z)‖ ≤
          ‖B‖ * ‖I w‖ * ‖I w‖ *
            ‖(v0 + Q z) - (v0 + Q w)‖ * ‖v0 + Q z‖ := hB _ _ _ _
      _ ≤ ‖B‖ * M * M * (‖Q‖ * ‖z - w‖) * S := by
        gcongr
      _ = ‖B‖ * (M ^ 2 * ‖Q‖ * S) * ‖z - w‖ := by ring
  have he4bound :
      ‖e4‖ ≤ ‖B‖ * (M ^ 2 * ‖Q‖ * S) * ‖z - w‖ := by
    dsimp [e4]
    rw [he4]
    calc
      ‖B (I w) (I w) (v0 + Q w)
          ((v0 + Q z) - (v0 + Q w))‖ ≤
          ‖B‖ * ‖I w‖ * ‖I w‖ * ‖v0 + Q w‖ *
            ‖(v0 + Q z) - (v0 + Q w)‖ := hB _ _ _ _
      _ ≤ ‖B‖ * M * M * S * (‖Q‖ * ‖z - w‖) := by
        gcongr
      _ = ‖B‖ * (M ^ 2 * ‖Q‖ * S) * ‖z - w‖ := by ring

  let q0 := B (I z) (I z) (v0 + Q z) (v0 + Q z)
  let q1 := B (I w) (I z) (v0 + Q z) (v0 + Q z)
  let q2 := B (I w) (I w) (v0 + Q z) (v0 + Q z)
  let q3 := B (I w) (I w) (v0 + Q w) (v0 + Q z)
  let q4 := B (I w) (I w) (v0 + Q w) (v0 + Q w)
  have htri : ‖q0 - q4‖ ≤ ‖e1‖ + ‖e2‖ + ‖e3‖ + ‖e4‖ := by
    calc
      ‖q0 - q4‖ = dist q0 q4 := by simp only [dist_eq_norm]
      _ ≤ dist q0 q1 + dist q1 q4 := dist_triangle _ _ _
      _ ≤ dist q0 q1 + (dist q1 q2 + dist q2 q4) := by
        exact add_le_add_right (dist_triangle q1 q2 q4) (dist q0 q1)
      _ ≤ dist q0 q1 + (dist q1 q2 + (dist q2 q3 + dist q3 q4)) := by
        exact add_le_add_right
          (add_le_add_right (dist_triangle q2 q3 q4) (dist q1 q2)) (dist q0 q1)
      _ = ‖e1‖ + ‖e2‖ + ‖e3‖ + ‖e4‖ := by
        simp only [dist_eq_norm, q0, q1, q2, q3, q4, e1, e2, e3, e4]
        ring
  calc
    ‖B (I z) (I z) (v0 + Q z) (v0 + Q z) -
        B (I w) (I w) (v0 + Q w) (v0 + Q w)‖ ≤
        ‖e1‖ + ‖e2‖ + ‖e3‖ + ‖e4‖ := by
      simpa only [q0, q4] using htri
    _ ≤ ‖B‖ * (M * K * S ^ 2) * ‖z - w‖ +
        ‖B‖ * (M * K * S ^ 2) * ‖z - w‖ +
        ‖B‖ * (M ^ 2 * ‖Q‖ * S) * ‖z - w‖ +
        ‖B‖ * (M ^ 2 * ‖Q‖ * S) * ‖z - w‖ := by
      gcongr
    _ = ‖B‖ * (2 * M * K * S ^ 2 + 2 * M ^ 2 * ‖Q‖ * S) * ‖z - w‖ := by
      ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.AffineQuadrilinearEstimate
