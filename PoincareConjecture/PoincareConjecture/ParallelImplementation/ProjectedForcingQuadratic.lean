import PoincareConjecture.ParallelImplementation.ForcingQuadraticNonlinearity
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ProjectedForcingQuadratic
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
/-- A genuine linear projection into a Holder graph induces a controlled quadratic forcing. -/
theorem exists_projected_forcing_quadratic
    {Y V Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T alpha : ℝ) (B : V →L[ℝ] V →L[ℝ] Z)
    (X : Submodule ℝ (ForcingJet Z T))
    (hX : (X : Set (ForcingJet Z T)) = forcingGraph Z T alpha)
    (P : Y →L[ℝ] ForcingJet V T)
    (hP : ∀ z : Y, P z ∈ forcingGraph V T alpha) :
    ∃ N : Y → X, N 0 = 0 ∧
      (∀ z : Y, ∀ p : Slab T, (N z).1.1 p = B ((P z).1 p) ((P z).1 p)) ∧
      ∀ z w : Y, ‖N z-N w‖ ≤
        (2*‖B‖*‖P‖^2)*(‖z‖+‖w‖)*‖z-w‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let Q : ForcingJet V T → ForcingJet Z T :=
    Classical.choose
      (PoincareConjecture.ParallelImplementation.ForcingQuadraticNonlinearity.exists_forcing_quadratic_nonlinearity
        B T alpha)
  have hQ := Classical.choose_spec
    (PoincareConjecture.ParallelImplementation.ForcingQuadraticNonlinearity.exists_forcing_quadratic_nonlinearity
      B T alpha)
  let N : Y → X := fun z =>
    ⟨Q (P z), by
      have hmem : Q (P z) ∈ forcingGraph Z T alpha :=
        (hQ.2 (P z) (hP z)).1
      rw [← hX] at hmem
      exact hmem⟩
  refine ⟨N, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change Q (P 0) = 0
    rw [P.map_zero]
    change Classical.choose
      (PoincareConjecture.ParallelImplementation.ForcingQuadraticNonlinearity.exists_forcing_quadratic_nonlinearity
        B T alpha) 0 = 0
    exact hQ.1
  · intro z p
    change (Q (P z)).1 p = B ((P z).1 p) ((P z).1 p)
    exact (hQ.2 (P z) (hP z)).2.1 p
  · intro z w
    change ‖Q (P z) - Q (P w)‖ ≤
      (2 * ‖B‖ * ‖P‖ ^ 2) * (‖z‖ + ‖w‖) * ‖z - w‖
    have hQlip := (hQ.2 (P z) (hP z)).2.2.2.2 (P w) (hP w)
    have hsum : ‖P z‖ + ‖P w‖ ≤ ‖P‖ * (‖z‖ + ‖w‖) := by
      calc
        ‖P z‖ + ‖P w‖ ≤ ‖P‖ * ‖z‖ + ‖P‖ * ‖w‖ :=
          add_le_add (P.le_opNorm z) (P.le_opNorm w)
        _ = ‖P‖ * (‖z‖ + ‖w‖) := by ring
    have hdiff : ‖P z - P w‖ ≤ ‖P‖ * ‖z - w‖ := by
      rw [← P.map_sub]
      exact P.le_opNorm (z - w)
    calc
      ‖Q (P z) - Q (P w)‖ ≤
          (2 * ‖B‖) * ((‖P z‖ + ‖P w‖) * ‖P z - P w‖) := by
            calc
              ‖Q (P z) - Q (P w)‖ ≤
                  2 * ‖B‖ * (‖P z‖ + ‖P w‖) * ‖P z - P w‖ := hQlip
              _ = (2 * ‖B‖) * ((‖P z‖ + ‖P w‖) * ‖P z - P w‖) := by ring
      _ ≤ (2 * ‖B‖) *
          ((‖P‖ * (‖z‖ + ‖w‖)) * (‖P‖ * ‖z - w‖)) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul hsum hdiff (norm_nonneg _) (by positivity)
            · positivity
      _ = (2 * ‖B‖ * ‖P‖ ^ 2) *
          (‖z‖ + ‖w‖) * ‖z - w‖ := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ProjectedForcingQuadratic
