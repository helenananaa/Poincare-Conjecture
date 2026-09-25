import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.AffineRightInverseFixedPoint
import PoincareConjecture.ParallelImplementation.AffineInverseQuadraticGradient
import PoincareConjecture.ParallelImplementation.AffineInverseHessianNonlinearity
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoupledAffineParabolicFixedPoint
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance standardGroup0 : NormedAddCommGroup (E3 →L[ℝ] E3) := inferInstance
local instance standardSpace0 : NormedSpace ℝ (E3 →L[ℝ] E3) := inferInstance
local instance standardGroup1 : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
local instance standardSpace1 : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
local instance standardGroup2 : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace2 : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup3 : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace3 : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup4 : NormedAddCommGroup ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace4 : NormedSpace ℝ ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup5 : NormedAddCommGroup ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace5 : NormedSpace ℝ ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
theorem exists_coupled_affine_operator_solution
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (T alpha R : ℝ) (hR : 0 < R)
    (X : Submodule ℝ (ForcingJet E6 T)) (hX : (X : Set (ForcingJet E6 T))=forcingGraph E6 T alpha)
    (L : Y →L[ℝ] X) (D : X →L[ℝ] Y) (hLD : L.comp D=ContinuousLinearMap.id ℝ X) (f : X)
    (B : (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ]
      (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6)
    (a : ForcingJet (E3 →L[ℝ] E3) T) (v0 : ForcingJet (E3 →L[ℝ] E6) T)
    (H0 : ForcingJet (E3 →L[ℝ] E3 →L[ℝ] E6) T)
    (ha : a ∈ forcingGraph (E3 →L[ℝ] E3) T alpha)
    (hv : v0 ∈ forcingGraph (E3 →L[ℝ] E6) T alpha)
    (hH : H0 ∈ forcingGraph (E3 →L[ℝ] E3 →L[ℝ] E6) T alpha)
    (P : Y →L[ℝ] ForcingJet (E3 →L[ℝ] E3) T)
    (Q : Y →L[ℝ] ForcingJet (E3 →L[ℝ] E6) T)
    (H : Y →L[ℝ] ForcingJet (E3 →L[ℝ] E3 →L[ℝ] E6) T)
    (hP : ∀ z, P z ∈ forcingGraph (E3 →L[ℝ] E3) T alpha)
    (hQ : ∀ z, Q z ∈ forcingGraph (E3 →L[ℝ] E6) T alpha)
    (hHmap : ∀ z, H z ∈ forcingGraph (E3 →L[ℝ] E3 →L[ℝ] E6) T alpha)
    (hsmall : ‖a‖+‖P‖*R ≤ 1/2)
    (hself : ‖D‖*(‖f‖+72*‖a‖*‖H0‖+32*‖B‖*‖v0‖^2+(18*(12*‖P‖*(‖H0‖+‖H‖*R)+(4*‖a‖+12*‖P‖*R)*‖H‖)+384*‖B‖*‖P‖*(‖v0‖+‖Q‖*R)^2+64*‖B‖*‖Q‖*(‖v0‖+‖Q‖*R))*R) ≤ R)
    (hcontract : ‖D‖*(18*(12*‖P‖*(‖H0‖+‖H‖*R)+(4*‖a‖+12*‖P‖*R)*‖H‖)+384*‖B‖*‖P‖*(‖v0‖+‖Q‖*R)^2+64*‖B‖*‖Q‖*(‖v0‖+‖Q‖*R)) < 1) :

    ∃ z : Y, ‖z‖ ≤ R ∧ ∃ b : ForcingJet (E3 →L[ℝ] E3) T,
      b ∈ forcingGraph (E3 →L[ℝ] E3) T alpha ∧ ‖b‖ ≤ 2 ∧
      ∀ p : Slab T, ((1-(a+P z).1 p)*b.1 p=1 ∧ b.1 p*(1-(a+P z).1 p)=1) ∧
        (L z).1.1 p = f.1.1 p +
          (∑ i : Fin 3, ∑ j : Fin 3, ((b.1 p-1) (EuclideanSpace.single j 1)) i •
            (H0+H z).1 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
          B (b.1 p) (b.1 p) ((v0+Q z).1 p) ((v0+Q z).1 p) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let K : ℝ :=
    18 * (12 * ‖P‖ * (‖H0‖ + ‖H‖ * R) +
      (4 * ‖a‖ + 12 * ‖P‖ * R) * ‖H‖) +
      384 * ‖B‖ * ‖P‖ * (‖v0‖ + ‖Q‖ * R) ^ 2 +
      64 * ‖B‖ * ‖Q‖ * (‖v0‖ + ‖Q‖ * R)
  obtain ⟨IH, NH, hIH, hIHzero, hNHcoord, hNHzero, hNHlip⟩ :=
    PoincareConjecture.ParallelImplementation.AffineInverseHessianNonlinearity.exists_affine_inverse_hessian_nonlinearity
      T alpha R hR X hX a ha P hP hsmall H0 hH H hHmap
  obtain ⟨IB, NB, hIB, hNBzero, hNBlip⟩ :=
    PoincareConjecture.ParallelImplementation.AffineInverseQuadraticGradient.exists_affine_inverse_quadratic_gradient
      (Y := Y) (A := E3 →L[ℝ] E3) (V := E3 →L[ℝ] E6) (Z := E6)
      T alpha R hR X hX B a v0 ha hv P Q hP hQ hsmall

  have hinv_eq (z : Y) (hz : ‖z‖ ≤ R) (p : Slab T) :
      (IH z).1 p = (IB z).1 p := by
    have hHinv := (hIH z hz).2.2.1 p
    have hBinv := (hIB z hz).2.2.1 p
    calc
      (IH z).1 p = (IH z).1 p * 1 := by simp
      _ = (IH z).1 p * ((1 - (a + P z).1 p) * (IB z).1 p) := by
        rw [hBinv.1]
      _ = ((IH z).1 p * (1 - (a + P z).1 p)) * (IB z).1 p := by
        rw [mul_assoc]
      _ = 1 * (IB z).1 p := by rw [hHinv.2]
      _ = (IB z).1 p := by simp

  let N : Y → X := fun z => NH z + NB z

  have hNcoord (z : Y) (hz : ‖z‖ ≤ R) (p : Slab T) :
      (N z).1.1 p =
        (∑ i : Fin 3, ∑ j : Fin 3,
          (((IH z).1 p - 1) (EuclideanSpace.single j 1)) i •
            (H0 + H z).1 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
          B ((IH z).1 p) ((IH z).1 p) ((v0 + Q z).1 p) ((v0 + Q z).1 p) := by
    dsimp [N]
    change (NH z).1.1 p + (NB z).1.1 p = _
    rw [hNHcoord z hz p, (hIB z hz).2.2.2 p, hinv_eq z hz p]
    simp only [Prod.fst_add, BoundedContinuousFunction.add_apply,
      ContinuousLinearMap.add_apply]

  have hNzero :
      ‖N 0‖ ≤ 72 * ‖a‖ * ‖H0‖ + 32 * ‖B‖ * ‖v0‖ ^ 2 := by
    calc
      ‖N 0‖ = ‖NH 0 + NB 0‖ := by rfl
      _ ≤ ‖NH 0‖ + ‖NB 0‖ := norm_add_le _ _
      _ ≤ 72 * ‖a‖ * ‖H0‖ + 32 * ‖B‖ * ‖v0‖ ^ 2 :=
        add_le_add hNHzero hNBzero

  have hK : 0 ≤ K := by
    dsimp [K]
    positivity

  have hNlip (z w : Y) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
      ‖N z - N w‖ ≤ K * ‖z - w‖ := by
    calc
      ‖N z - N w‖ = ‖(NH z - NH w) + (NB z - NB w)‖ := by
        congr 1
        dsimp [N]
        abel
      _ ≤ ‖NH z - NH w‖ + ‖NB z - NB w‖ := norm_add_le _ _
      _ ≤
          (18 * (12 * ‖P‖ * (‖H0‖ + ‖H‖ * R) +
            (4 * ‖a‖ + 12 * ‖P‖ * R) * ‖H‖)) * ‖z - w‖ +
          (384 * ‖B‖ * ‖P‖ * (‖v0‖ + ‖Q‖ * R) ^ 2 +
            64 * ‖B‖ * ‖Q‖ * (‖v0‖ + ‖Q‖ * R)) * ‖z - w‖ :=
        add_le_add (hNHlip z w hz hw) (hNBlip z w hz hw)
      _ = K * ‖z - w‖ := by
        dsimp [K]
        ring

  have hinner :
      ‖f + N 0‖ + K * R ≤
        ‖f‖ + 72 * ‖a‖ * ‖H0‖ + 32 * ‖B‖ * ‖v0‖ ^ 2 + K * R := by
    have hnormsum :
        ‖f‖ + ‖N 0‖ ≤ ‖f‖ + (72 * ‖a‖ * ‖H0‖ + 32 * ‖B‖ * ‖v0‖ ^ 2) := by
      exact add_le_add_right hNzero ‖f‖
    calc
      ‖f + N 0‖ + K * R ≤ (‖f‖ + ‖N 0‖) + K * R :=
        add_le_add_left (norm_add_le f (N 0)) _
      _ ≤ (‖f‖ + (72 * ‖a‖ * ‖H0‖ + 32 * ‖B‖ * ‖v0‖ ^ 2)) + K * R :=
        add_le_add_left hnormsum _
      _ = ‖f‖ + 72 * ‖a‖ * ‖H0‖ + 32 * ‖B‖ * ‖v0‖ ^ 2 + K * R := by ring

  have hself' : ‖D‖ * (‖f + N 0‖ + K * R) ≤ R := by
    calc
      ‖D‖ * (‖f + N 0‖ + K * R) ≤
          ‖D‖ * (‖f‖ + 72 * ‖a‖ * ‖H0‖ +
            32 * ‖B‖ * ‖v0‖ ^ 2 + K * R) :=
        mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
      _ ≤ R := by simpa [K] using hself

  have hcontract' : ‖D‖ * K < 1 := by
    simpa [K] using hcontract

  obtain ⟨z, hz, hfix, hLz, _⟩ :=
    PoincareConjecture.ParallelImplementation.AffineRightInverseFixedPoint.affine_right_inverse_fixed_point
      L D hLD N f K R hK hR hNlip hself' hcontract'

  refine ⟨z, hz, IH z, (hIH z hz).1, (hIH z hz).2.1, ?_⟩
  intro p
  refine ⟨(hIH z hz).2.2.1 p, ?_⟩
  have hvalue : (L z).1.1 p = f.1.1 p + (N z).1.1 p := by
    have hh := congrArg (fun x : X => ((x : ForcingJet E6 T).1 p)) hLz
    simpa using hh
  rw [hvalue, hNcoord z hz p]
  simp only [add_assoc]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoupledAffineParabolicFixedPoint
