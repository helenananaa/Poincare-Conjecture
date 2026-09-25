import PoincareConjecture.ParallelImplementation.ProjectedFullInverseBall
import PoincareConjecture.ParallelImplementation.ForcingGraphQuadrilinearLift
import PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint
import PoincareConjecture.ParallelImplementation.AffineForcingGraphInverse
import PoincareConjecture.ParallelImplementation.AffineQuadrilinearEstimate
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.AffineInverseQuadraticGradient
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
theorem exists_affine_inverse_quadratic_gradient
    {Y A V Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [CompleteSpace A]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T alpha R : ℝ) (hR : 0 < R)
    (X : Submodule ℝ (ForcingJet Z T)) (hX : (X : Set (ForcingJet Z T))=forcingGraph Z T alpha)
    (B : A →L[ℝ] A →L[ℝ] V →L[ℝ] V →L[ℝ] Z)
    (a : ForcingJet A T) (v0 : ForcingJet V T)
    (ha : a ∈ forcingGraph A T alpha) (hv0 : v0 ∈ forcingGraph V T alpha)
    (P : Y →L[ℝ] ForcingJet A T) (Q : Y →L[ℝ] ForcingJet V T)
    (hP : ∀ z : Y, P z ∈ forcingGraph A T alpha)
    (hQ : ∀ z : Y, Q z ∈ forcingGraph V T alpha) (hsmall : ‖a‖+‖P‖*R ≤ 1/2) :

    let S : ℝ := ‖v0‖+‖Q‖*R
    ∃ I : Y → ForcingJet A T, ∃ N : Y → X,
      (∀ z : Y, ‖z‖ ≤ R → I z ∈ forcingGraph A T alpha ∧ ‖I z‖ ≤ 2 ∧
        (∀ p : Slab T, (1-(a+P z).1 p)*(I z).1 p=1 ∧ (I z).1 p*(1-(a+P z).1 p)=1) ∧
        ∀ p : Slab T, (N z).1.1 p = B ((I z).1 p) ((I z).1 p) ((v0+Q z).1 p) ((v0+Q z).1 p)) ∧
      ‖N 0‖ ≤ 32*‖B‖*‖v0‖^2 ∧
      ∀ z w : Y, ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖N z-N w‖ ≤ (384*‖B‖*‖P‖*S^2+64*‖B‖*‖Q‖*S)*‖z-w‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨L, hLnorm, hLvalue, hLgraph⟩ :=
    PoincareConjecture.ParallelImplementation.ForcingGraphQuadrilinearLift.exists_forcing_graph_quadrilinear_lift
      (B := B) T alpha
  obtain ⟨I, hIspec, hIlip⟩ :=
    PoincareConjecture.ParallelImplementation.AffineForcingGraphInverse.exists_affine_forcing_graph_inverse
      (A := A) T alpha R hR a ha P hP hsmall

  have hVsum (z : Y) : v0 + Q z ∈ forcingGraph V T alpha := by
    intro p
    change v0.2 p + (Q z).2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (v0.1 p.1.1 + (Q z).1 p.1.1 -
          (v0.1 p.1.2 + (Q z).1 p.1.2))
    rw [hv0 p, hQ z p]
    simp only [smul_sub, smul_add]
    abel

  let N : Y → X := fun z =>
    if hz : ‖z‖ ≤ R then
      ⟨L (I z) (I z) (v0 + Q z) (v0 + Q z), by
        change L (I z) (I z) (v0 + Q z) (v0 + Q z) ∈
          (X : Set (ForcingJet Z T))
        rw [hX]
        exact hLgraph (I z) (hIspec z hz).1
          (I z) (hIspec z hz).1
          (v0 + Q z) (hVsum z)
          (v0 + Q z) (hVsum z)⟩
    else 0

  have hNbranch (z : Y) (hz : ‖z‖ ≤ R) :
      (N z : ForcingJet Z T) = L (I z) (I z) (v0 + Q z) (v0 + Q z) := by
    simp [N, hz]

  have hzeroBall : ‖(0 : Y)‖ ≤ R := by
    simpa using hR.le

  have hLpoint (x y : ForcingJet A T) (v w : ForcingJet V T) :
      ‖L x y v w‖ ≤ ‖L‖ * ‖x‖ * ‖y‖ * ‖v‖ * ‖w‖ := by
    calc
      ‖L x y v w‖ ≤ ‖L x y v‖ * ‖w‖ := (L x y v).le_opNorm w
      _ ≤ (‖L x y‖ * ‖v‖) * ‖w‖ := by
        gcongr
        exact (L x y).le_opNorm v
      _ ≤ ((‖L x‖ * ‖y‖) * ‖v‖) * ‖w‖ := by
        gcongr
        exact (L x).le_opNorm y
      _ ≤ (((‖L‖ * ‖x‖) * ‖y‖) * ‖v‖) * ‖w‖ := by
        gcongr
        exact L.le_opNorm x

  refine ⟨I, N, ?_, ?_, ?_⟩
  · intro z hz
    have hi := hIspec z hz
    refine ⟨hi.1, hi.2.1, hi.2.2, ?_⟩
    intro p
    rw [hNbranch z hz]
    exact hLvalue (I z) (I z) (v0 + Q z) (v0 + Q z) p
  · change ‖(N 0 : ForcingJet Z T)‖ ≤ 32 * ‖B‖ * ‖v0‖ ^ 2
    rw [hNbranch 0 hzeroBall, Q.map_zero, add_zero]
    calc
      ‖L (I 0) (I 0) v0 v0‖ ≤
          ‖L‖ * ‖I 0‖ * ‖I 0‖ * ‖v0‖ * ‖v0‖ := hLpoint _ _ _ _
      _ ≤ (8 * ‖B‖) * 2 * 2 * ‖v0‖ * ‖v0‖ := by
        gcongr
        · exact (hIspec 0 hzeroBall).2.1
        · exact (hIspec 0 hzeroBall).2.1
      _ = 32 * ‖B‖ * ‖v0‖ ^ 2 := by ring
  · intro z w hz hw
    change ‖(N z : ForcingJet Z T) - (N w : ForcingJet Z T)‖ ≤ _
    rw [hNbranch z hz, hNbranch w hw]
    let S : ℝ := ‖v0‖ + ‖Q‖ * R
    have hgrad :=
      PoincareConjecture.ParallelImplementation.AffineQuadrilinearEstimate.affine_quadrilinear_lipschitz
        (B := L) (I := I) (Q := Q) (v0 := v0) (M := 2)
        (K := 12 * ‖P‖) (R := R) (by norm_num) (by positivity) hR
        (fun x hx => (hIspec x hx).2.1)
        (fun x y hx hy => hIlip.2 x y hx hy) z w hz hw
    have hgrad' :
        ‖L (I z) (I z) (v0 + Q z) (v0 + Q z) -
          L (I w) (I w) (v0 + Q w) (v0 + Q w)‖ ≤
        ‖L‖ * (48 * ‖P‖ * S ^ 2 + 8 * ‖Q‖ * S) * ‖z - w‖ := by
      convert hgrad using 1; ring
    have hS : 0 ≤ S := by
      dsimp [S]
      positivity
    have hcoef : 0 ≤ 48 * ‖P‖ * S ^ 2 + 8 * ‖Q‖ * S := by
      positivity
    calc
      ‖L (I z) (I z) (v0 + Q z) (v0 + Q z) -
          L (I w) (I w) (v0 + Q w) (v0 + Q w)‖ ≤
          ‖L‖ * (48 * ‖P‖ * S ^ 2 + 8 * ‖Q‖ * S) * ‖z - w‖ := hgrad'
      _ ≤ (8 * ‖B‖) * (48 * ‖P‖ * S ^ 2 + 8 * ‖Q‖ * S) * ‖z - w‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hLnorm hcoef
        · exact norm_nonneg _
      _ = (384 * ‖B‖ * ‖P‖ * S ^ 2 + 64 * ‖B‖ * ‖Q‖ * S) * ‖z - w‖ := by
        ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.AffineInverseQuadraticGradient
