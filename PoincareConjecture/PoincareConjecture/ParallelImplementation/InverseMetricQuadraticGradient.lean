import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.ForcingGraphQuadrilinearLift
import PoincareConjecture.ParallelImplementation.QuadrilinearCoefficientGradientEstimate
import PoincareConjecture.ParallelImplementation.ProjectedFullInverseBall
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.InverseMetricQuadraticGradient
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
theorem exists_inverse_metric_quadratic_gradient
    {Y A V Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [CompleteSpace A]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T alpha R : ℝ) (hR : 0 < R)
    (X : Submodule ℝ (ForcingJet Z T))
    (hX : (X : Set (ForcingJet Z T)) = forcingGraph Z T alpha)
    (B : A →L[ℝ] A →L[ℝ] V →L[ℝ] V →L[ℝ] Z)
    (P : Y →L[ℝ] ForcingJet A T) (Q : Y →L[ℝ] ForcingJet V T)
    (hP : ∀ z : Y, P z ∈ forcingGraph A T alpha)
    (hQ : ∀ z : Y, Q z ∈ forcingGraph V T alpha) (hsmall : ‖P‖*R ≤ 1/2) :
    ∃ N : Y → X, N 0=0 ∧
      (∀ z : Y, ‖z‖ ≤ R → ∃ b : ForcingJet A T,
        b ∈ forcingGraph A T alpha ∧ ‖b‖ ≤ 2 ∧
        (∀ p : Slab T, (1-(P z).1 p)*b.1 p=1 ∧ b.1 p*(1-(P z).1 p)=1) ∧
        (∀ p : Slab T, (N z).1.1 p = B (b.1 p) (b.1 p) ((Q z).1 p) ((Q z).1 p))) ∧
      (∀ z w : Y, ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖N z-N w‖ ≤ (224*‖B‖*‖Q‖^2)*(‖z‖+‖w‖)*‖z-w‖) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨L, hLnorm, hLvalue, hLgraph⟩ :=
    PoincareConjecture.ParallelImplementation.ForcingGraphQuadrilinearLift.exists_forcing_graph_quadrilinear_lift
      (B := B) T alpha
  obtain ⟨I, hIzero, hIspec, hIlip⟩ :=
    PoincareConjecture.ParallelImplementation.ProjectedFullInverseBall.exists_projected_full_inverse_ball
      (A := A) T alpha R hR P hP hsmall
  let N : Y → X := fun z =>
    if hz : ‖z‖ ≤ R then
      ⟨L (I z) (I z) (Q z) (Q z), by
        change L (I z) (I z) (Q z) (Q z) ∈ (X : Set (ForcingJet Z T))
        rw [hX]
        exact hLgraph (I z) (hIspec z hz).1 (I z) (hIspec z hz).1
          (Q z) (hQ z) (Q z) (hQ z)⟩
    else 0
  have hzeroBall : ‖(0 : Y)‖ ≤ R := by
    simpa using hR.le
  have hNbranch (z : Y) (hz : ‖z‖ ≤ R) :
      (N z : ForcingJet Z T) = L (I z) (I z) (Q z) (Q z) := by
    simp [N, hz]
  have hKR : (12 * ‖P‖) * R ≤ 6 := by
    calc
      (12 * ‖P‖) * R = 12 * (‖P‖ * R) := by ring
      _ ≤ 12 * (1 / 2) := by nlinarith [hsmall]
      _ = 6 := by norm_num
  have hcoef :
      ‖L‖ * (2 ^ 2 + 2 * 2 * (12 * ‖P‖) * R) * ‖Q‖ ^ 2 ≤
        224 * ‖B‖ * ‖Q‖ ^ 2 := by
    have hfactor : 2 ^ 2 + 2 * 2 * (12 * ‖P‖) * R ≤ 28 := by
      nlinarith [hKR]
    calc
      ‖L‖ * (2 ^ 2 + 2 * 2 * (12 * ‖P‖) * R) * ‖Q‖ ^ 2 ≤
          (8 * ‖B‖) * 28 * ‖Q‖ ^ 2 := by
        gcongr
      _ = 224 * ‖B‖ * ‖Q‖ ^ 2 := by ring
  refine ⟨N, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [hNbranch 0 hzeroBall]
    simp [Q.map_zero]
  · intro z hz
    refine ⟨I z, (hIspec z hz).1, (hIspec z hz).2.1,
      (hIspec z hz).2.2, ?_⟩
    intro p
    rw [hNbranch z hz]
    exact hLvalue (I z) (I z) (Q z) (Q z) p
  · intro z w hz hw
    change ‖(N z : ForcingJet Z T) - (N w : ForcingJet Z T)‖ ≤ _
    rw [hNbranch z hz, hNbranch w hw]
    have hgrad :=
      PoincareConjecture.ParallelImplementation.QuadrilinearCoefficientGradientEstimate.quadrilinear_coefficient_gradient_estimate
        (B := L) (I := I) (P := Q) (M := 2)
        (K := 12 * ‖P‖) (R := R) (by norm_num) (by positivity) hR
        (fun x hx => (hIspec x hx).2.1)
        (fun x y hx hy => hIlip x y hx hy) z w hz hw
    calc
      ‖L (I z) (I z) (Q z) (Q z) -
          L (I w) (I w) (Q w) (Q w)‖ ≤
        (‖L‖ * (2 ^ 2 + 2 * 2 * (12 * ‖P‖) * R) * ‖Q‖ ^ 2) *
          (‖z‖ + ‖w‖) * ‖z - w‖ := hgrad
      _ ≤ (224 * ‖B‖ * ‖Q‖ ^ 2) * (‖z‖ + ‖w‖) * ‖z - w‖ := by
        gcongr
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.InverseMetricQuadraticGradient
