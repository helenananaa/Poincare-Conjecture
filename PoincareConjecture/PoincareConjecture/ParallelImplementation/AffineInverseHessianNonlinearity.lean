import PoincareConjecture.ParallelImplementation.AffineForcingGraphBilinearProduct
import PoincareConjecture.ParallelImplementation.AffineInverseCorrectionBound
import PoincareConjecture.ParallelImplementation.OperatorHessianContraction
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.AffineInverseHessianNonlinearity
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_affine_inverse_hessian_nonlinearity
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T alpha R : ℝ) (hR : 0 < R)
    (X : Submodule ℝ (ForcingJet E6 T))
    (hX : (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha)
    (a : ForcingJet (E3 →L[ℝ] E3) T)
    (ha : a ∈ forcingGraph (E3 →L[ℝ] E3) T alpha)
    (P : Y →L[ℝ] ForcingJet (E3 →L[ℝ] E3) T)
    (hP : ∀ z, P z ∈ forcingGraph (E3 →L[ℝ] E3) T alpha)
    (hsmall : ‖a‖+‖P‖*R ≤ 1/2)
    (H0 : ForcingJet (E3 →L[ℝ] E3 →L[ℝ] E6) T)
    (hH0 : H0 ∈ forcingGraph (E3 →L[ℝ] E3 →L[ℝ] E6) T alpha)
    (Q : Y →L[ℝ] ForcingJet (E3 →L[ℝ] E3 →L[ℝ] E6) T)
    (hQ : ∀ z, Q z ∈ forcingGraph (E3 →L[ℝ] E3 →L[ℝ] E6) T alpha) :
    let oneJet : ForcingJet (E3 →L[ℝ] E3) T :=
      ((1 : Slab T →ᵇ (E3 →L[ℝ] E3)), (0 : Pair T →ᵇ (E3 →L[ℝ] E3)))
    ∃ I : Y → ForcingJet (E3 →L[ℝ] E3) T, ∃ N : Y → X,
        (∀ z, ‖z‖ ≤ R →
          I z ∈ forcingGraph (E3 →L[ℝ] E3) T alpha ∧ ‖I z‖ ≤ 2 ∧
          (∀ p : Slab T, (1-(a+P z).1 p)*(I z).1 p=1 ∧
            (I z).1 p*(1-(a+P z).1 p)=1) ∧
          ‖I z-oneJet‖ ≤ 4*‖a+P z‖) ∧
        ‖I 0-oneJet‖ ≤ 4*‖a‖ ∧
        (∀ z, ‖z‖ ≤ R → ∀ p : Slab T,
          (N z).1.1 p =
            ∑ i : Fin 3, ∑ j : Fin 3,
              (((I z).1 p-1) (EuclideanSpace.single j 1)) i •
                (H0+Q z).1 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
        ‖N 0‖ ≤ 72*‖a‖*‖H0‖ ∧
        (∀ z w, ‖z‖ ≤ R → ‖w‖ ≤ R →
          ‖N z-N w‖ ≤
            (18*(12*‖P‖*(‖H0‖+‖Q‖*R)+
              (4*‖a‖+12*‖P‖*R)*‖Q‖))*‖z-w‖) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let oneJet : ForcingJet (E3 →L[ℝ] E3) T :=
    ((1 : Slab T →ᵇ (E3 →L[ℝ] E3)), (0 : Pair T →ᵇ (E3 →L[ℝ] E3)))
  obtain ⟨I, hI, hIzero, hIlip⟩ :=
    PoincareConjecture.ParallelImplementation.AffineInverseCorrectionBound.exists_affine_inverse_correction_bound
      T alpha R hR a ha P hP hsmall
  have hzeroBall : ‖(0 : Y)‖ ≤ R := by
    simpa using hR.le
  let a0 : ForcingJet (E3 →L[ℝ] E3) T := I 0 - oneJet
  let J : Y → ForcingJet (E3 →L[ℝ] E3) T := fun z => I z - I 0
  have ha0Graph : a0 ∈ forcingGraph (E3 →L[ℝ] E3) T alpha := by
    dsimp [a0]
    intro p
    change (I 0).2 p - oneJet.2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((I 0).1 p.1.1 - oneJet.1 p.1.1 -
          ((I 0).1 p.1.2 - oneJet.1 p.1.2))
    rw [(hI 0 hzeroBall).1 p]
    simp [oneJet]
  have hJ0 : J 0 = 0 := by
    simp [J]
  have hJGraph (z : Y) (hz : ‖z‖ ≤ R) :
      J z ∈ forcingGraph (E3 →L[ℝ] E3) T alpha := by
    dsimp [J]
    intro p
    change (I z).2 p - (I 0).2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((I z).1 p.1.1 - (I 0).1 p.1.1 -
          ((I z).1 p.1.2 - (I 0).1 p.1.2))
    rw [(hI z hz).1 p, (hI 0 hzeroBall).1 p]
    simp only [smul_sub]
    abel
  have hJLip (z w : Y) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
      ‖J z - J w‖ ≤ (12 * ‖P‖) * ‖z - w‖ := by
    calc
      ‖J z - J w‖ = ‖I z - I w‖ := by
        congr 1
        dsimp [J]
        abel
      _ ≤ (12 * ‖P‖) * ‖z - w‖ := hIlip z w hz hw
  have ha0Norm : ‖a0‖ ≤ 4 * ‖a‖ := by
    simpa [a0] using hIzero
  obtain ⟨B, hBnorm, hBcoord⟩ :=
    PoincareConjecture.ParallelImplementation.OperatorHessianContraction.exists_operator_hessian_contraction
      (V := E6)
  have htwoB : 2 * ‖B‖ ≤ 18 := by
    nlinarith [hBnorm]
  have hKnonneg : 0 ≤ (12 * ‖P‖ : ℝ) := by positivity
  obtain ⟨N, hNcoord, hNzero, hNlip⟩ :=
    PoincareConjecture.ParallelImplementation.AffineForcingGraphBilinearProduct.exists_affine_forcing_bilinear_product
      T alpha R (12 * ‖P‖) hR hKnonneg X hX B a0 H0 ha0Graph hH0
      J hJ0 hJGraph hJLip Q hQ
  have hcoeffJet (z : Y) : a0 + J z = I z - oneJet := by
    dsimp [a0, J]
    abel
  have hcoeffValue (z : Y) (p : Slab T) :
      (a0 + J z).1 p = (I z).1 p - 1 := by
    rw [hcoeffJet z]
    simp [oneJet, BoundedContinuousFunction.sub_apply]
  refine ⟨I, N, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hI z hz
  · exact hIzero
  · intro z hz p
    rw [hNcoord z hz p, hBcoord, hcoeffValue z p]
  · calc
      ‖N 0‖ ≤ 2 * ‖B‖ * ‖a0‖ * ‖H0‖ := hNzero
      _ ≤ (18 * ‖a0‖) * ‖H0‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right htwoB (norm_nonneg a0))
          (norm_nonneg H0)
      _ ≤ (18 * (4 * ‖a‖)) * ‖H0‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ha0Norm (by norm_num))
          (norm_nonneg H0)
      _ = 72 * ‖a‖ * ‖H0‖ := by ring
  · intro z w hz hw
    have hinner :
        12 * ‖P‖ * (‖H0‖ + ‖Q‖ * R) +
            (‖a0‖ + 12 * ‖P‖ * R) * ‖Q‖ ≤
          12 * ‖P‖ * (‖H0‖ + ‖Q‖ * R) +
            (4 * ‖a‖ + 12 * ‖P‖ * R) * ‖Q‖ := by
      gcongr
    have hinnerNonneg :
        0 ≤ 12 * ‖P‖ * (‖H0‖ + ‖Q‖ * R) +
          (‖a0‖ + 12 * ‖P‖ * R) * ‖Q‖ := by
      positivity
    calc
      ‖N z - N w‖ ≤
          (2 * ‖B‖ *
            (12 * ‖P‖ * (‖H0‖ + ‖Q‖ * R) +
              (‖a0‖ + 12 * ‖P‖ * R) * ‖Q‖)) * ‖z - w‖ :=
        hNlip z w hz hw
      _ ≤
          (18 *
            (12 * ‖P‖ * (‖H0‖ + ‖Q‖ * R) +
              (4 * ‖a‖ + 12 * ‖P‖ * R) * ‖Q‖)) * ‖z - w‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc
          2 * ‖B‖ *
              (12 * ‖P‖ * (‖H0‖ + ‖Q‖ * R) +
                (‖a0‖ + 12 * ‖P‖ * R) * ‖Q‖) ≤
            18 *
              (12 * ‖P‖ * (‖H0‖ + ‖Q‖ * R) +
                (‖a0‖ + 12 * ‖P‖ * R) * ‖Q‖) :=
              mul_le_mul_of_nonneg_right htwoB hinnerNonneg
          _ ≤
            18 *
              (12 * ‖P‖ * (‖H0‖ + ‖Q‖ * R) +
                (4 * ‖a‖ + 12 * ‖P‖ * R) * ‖Q‖) :=
              mul_le_mul_of_nonneg_left hinner (by norm_num)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.AffineInverseHessianNonlinearity
