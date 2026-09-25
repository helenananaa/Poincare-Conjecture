import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
import PoincareConjecture.ParallelImplementation.CoordinateDeTurckFourlinear
import PoincareConjecture.ParallelImplementation.CoordinateOperatorEntries
import PoincareConjecture.ParallelImplementation.SymmetricSixPacking
import PoincareConjecture.ParallelImplementation.SixGradientCoordinateEncoding
import PoincareConjecture.ParallelImplementation.CoordinateDeTurckSymmetry
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixCoordinateDeTurckNonlinearity
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open MorganTianLib.MetricCoefficient
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
theorem exists_concrete_six_deturck_nonlinearity :

    ∃ B : (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ]
      (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6,
      ‖B‖ ≤ 30000 ∧
      (∀ (H K : E3 →L[ℝ] E3) (A G : E3 →L[ℝ] E6),
        B H K A G = (let m : Mat := deturckQuadratic (fun i j : Idx => (H (EuclideanSpace.single j 1)) i) (fun i j : Idx => (K (EuclideanSpace.single j 1)) i) (fun a i j : Idx => symmetricSixMatrix (A (EuclideanSpace.single a 1)) i j) (fun a i j : Idx => symmetricSixMatrix (G (EuclideanSpace.single a 1)) i j)
          WithLp.toLp 2 ![m 0 0, m 1 1, m 2 2, m 0 1, m 0 2, m 1 2])) ∧
      ∀ (H : E3 →L[ℝ] E3) (A : E3 →L[ℝ] E6),
        (∀ i j : Idx, (H (EuclideanSpace.single j 1)) i = (H (EuclideanSpace.single i 1)) j) →
        ∀ i j : Idx, symmetricSixMatrix (B H H A A) i j = deturckQuadratic (fun i j : Idx => (H (EuclideanSpace.single j 1)) i) (fun i j : Idx => (H (EuclideanSpace.single j 1)) i) (fun a i j : Idx => symmetricSixMatrix (A (EuclideanSpace.single a 1)) i j) (fun a i j : Idx => symmetricSixMatrix (A (EuclideanSpace.single a 1)) i j) i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rcases PoincareConjecture.ParallelImplementation.CoordinateDeTurckFourlinear.exists_coordinate_deturck_fourlinear with
    ⟨Q, hQnorm, hQentry⟩
  rcases PoincareConjecture.ParallelImplementation.CoordinateOperatorEntries.exists_operator_entries with
    ⟨C, hCnorm, hCinj, hCentry, hCidentity, hCmul⟩
  rcases PoincareConjecture.ParallelImplementation.SixGradientCoordinateEncoding.exists_gradient_entries with
    ⟨D, hDnorm, hDentry, hDsymmetric⟩
  rcases PoincareConjecture.ParallelImplementation.SymmetricSixPacking.exists_symmetric_six_packing with
    ⟨P, hPnorm, hPentry, hProundtrip, hPsymmetric⟩

  let T₂ :
      (Mat →L[ℝ] (First →L[ℝ] First →L[ℝ] Mat)) →L[ℝ]
        ((E3 →L[ℝ] E3) →L[ℝ] (First →L[ℝ] First →L[ℝ] Mat)) :=
    (ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E3) Mat
      (First →L[ℝ] First →L[ℝ] Mat)).flip C
  let T₃ :
      (First →L[ℝ] First →L[ℝ] Mat) →L[ℝ]
        ((E3 →L[ℝ] E6) →L[ℝ] (First →L[ℝ] Mat)) :=
    (ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E6) First
      (First →L[ℝ] Mat)).flip D
  let T₄ : (First →L[ℝ] Mat) →L[ℝ] ((E3 →L[ℝ] E6) →L[ℝ] Mat) :=
    (ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E6) First Mat).flip D
  let T₅ : ((E3 →L[ℝ] E6) →L[ℝ] Mat) →L[ℝ]
      ((E3 →L[ℝ] E6) →L[ℝ] E6) :=
    ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E6) Mat E6 P
  let T₃lift :
      ((E3 →L[ℝ] E3) →L[ℝ] (First →L[ℝ] First →L[ℝ] Mat)) →L[ℝ]
        ((E3 →L[ℝ] E3) →L[ℝ]
          ((E3 →L[ℝ] E6) →L[ℝ] First →L[ℝ] Mat)) :=
    ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E3)
      (First →L[ℝ] First →L[ℝ] Mat)
      ((E3 →L[ℝ] E6) →L[ℝ] First →L[ℝ] Mat) T₃
  let T₄liftA :
      ((E3 →L[ℝ] E6) →L[ℝ] (First →L[ℝ] Mat)) →L[ℝ]
        ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] Mat) :=
    ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E6) (First →L[ℝ] Mat)
      ((E3 →L[ℝ] E6) →L[ℝ] Mat) T₄
  let T₄liftK :
      ((E3 →L[ℝ] E3) →L[ℝ]
        ((E3 →L[ℝ] E6) →L[ℝ] (First →L[ℝ] Mat))) →L[ℝ]
        ((E3 →L[ℝ] E3) →L[ℝ]
          ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] Mat)) :=
    ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E3)
      ((E3 →L[ℝ] E6) →L[ℝ] (First →L[ℝ] Mat))
      ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] Mat) T₄liftA
  let T₅liftA :
      ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] Mat) →L[ℝ]
        ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) :=
    ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E6)
      ((E3 →L[ℝ] E6) →L[ℝ] Mat)
      ((E3 →L[ℝ] E6) →L[ℝ] E6) T₅
  let T₅liftK :
      ((E3 →L[ℝ] E3) →L[ℝ]
        ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] Mat)) →L[ℝ]
        ((E3 →L[ℝ] E3) →L[ℝ]
          ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6)) :=
    ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E3)
      ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] Mat)
      ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) T₅liftA
  let Q₁ : (E3 →L[ℝ] E3) →L[ℝ]
      (Mat →L[ℝ] First →L[ℝ] First →L[ℝ] Mat) := Q.comp C
  let Q₂ := T₂.comp Q₁
  let Q₃ := T₃lift.comp Q₂
  let Q₄ := T₄liftK.comp Q₃
  let B := T₅liftK.comp Q₄

  have hT₂apply (f : Mat →L[ℝ] (First →L[ℝ] First →L[ℝ] Mat)) :
      ‖T₂ f‖ ≤ ‖f‖ := by
    change ‖f.comp C‖ ≤ ‖f‖
    calc
      ‖f.comp C‖ ≤ ‖f‖ * ‖C‖ := f.opNorm_comp_le C
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hCnorm (norm_nonneg _)
      _ = ‖f‖ := mul_one _
  have hT₂norm : ‖T₂‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound T₂ (by norm_num)
    intro f
    simpa using hT₂apply f

  have hT₃apply (f : First →L[ℝ] (First →L[ℝ] Mat)) :
      ‖T₃ f‖ ≤ ‖f‖ := by
    change ‖f.comp D‖ ≤ ‖f‖
    calc
      ‖f.comp D‖ ≤ ‖f‖ * ‖D‖ := f.opNorm_comp_le D
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hDnorm (norm_nonneg _)
      _ = ‖f‖ := mul_one _
  have hT₃norm : ‖T₃‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound T₃ (by norm_num)
    intro f
    simpa using hT₃apply f

  have hT₄apply (f : First →L[ℝ] Mat) : ‖T₄ f‖ ≤ ‖f‖ := by
    change ‖f.comp D‖ ≤ ‖f‖
    calc
      ‖f.comp D‖ ≤ ‖f‖ * ‖D‖ := f.opNorm_comp_le D
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hDnorm (norm_nonneg _)
      _ = ‖f‖ := mul_one _
  have hT₄norm : ‖T₄‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound T₄ (by norm_num)
    intro f
    simpa using hT₄apply f

  have hT₅apply (f : (E3 →L[ℝ] E6) →L[ℝ] Mat) :
      ‖T₅ f‖ ≤ 3 * ‖f‖ := by
    change ‖P.comp f‖ ≤ 3 * ‖f‖
    calc
      ‖P.comp f‖ ≤ ‖P‖ * ‖f‖ := P.opNorm_comp_le f
      _ ≤ 3 * ‖f‖ := mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
  have hT₅norm : ‖T₅‖ ≤ 3 := by
    apply ContinuousLinearMap.opNorm_le_bound T₅ (by norm_num)
    intro f
    simpa [mul_comm] using hT₅apply f

  have hT₃liftNorm : ‖T₃lift‖ ≤ 1 := by
    calc
      ‖T₃lift‖ ≤ ‖T₃‖ := by
        apply ContinuousLinearMap.opNorm_le_bound T₃lift (norm_nonneg T₃)
        intro f
        change ‖(ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E3)
          (First →L[ℝ] First →L[ℝ] Mat)
          ((E3 →L[ℝ] E6) →L[ℝ] First →L[ℝ] Mat) T₃) f‖ ≤
            ‖T₃‖ * ‖f‖
        rw [ContinuousLinearMap.compL_apply]
        exact T₃.opNorm_comp_le f
      _ ≤ 1 := hT₃norm
  have hT₄liftANorm : ‖T₄liftA‖ ≤ 1 := by
    calc
      ‖T₄liftA‖ ≤ ‖T₄‖ := by
        apply ContinuousLinearMap.opNorm_le_bound T₄liftA (norm_nonneg T₄)
        intro f
        change ‖(ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E6)
          (First →L[ℝ] Mat) ((E3 →L[ℝ] E6) →L[ℝ] Mat) T₄) f‖ ≤
            ‖T₄‖ * ‖f‖
        rw [ContinuousLinearMap.compL_apply]
        exact T₄.opNorm_comp_le f
      _ ≤ 1 := hT₄norm
  have hT₄liftKNorm : ‖T₄liftK‖ ≤ 1 := by
    calc
      ‖T₄liftK‖ ≤ ‖T₄liftA‖ := by
        apply ContinuousLinearMap.opNorm_le_bound T₄liftK (norm_nonneg T₄liftA)
        intro f
        change ‖(ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E3)
          ((E3 →L[ℝ] E6) →L[ℝ] (First →L[ℝ] Mat))
          ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] Mat) T₄liftA) f‖ ≤
            ‖T₄liftA‖ * ‖f‖
        rw [ContinuousLinearMap.compL_apply]
        exact T₄liftA.opNorm_comp_le f
      _ ≤ 1 := hT₄liftANorm
  have hT₅liftANorm : ‖T₅liftA‖ ≤ 3 := by
    calc
      ‖T₅liftA‖ ≤ ‖T₅‖ := by
        apply ContinuousLinearMap.opNorm_le_bound T₅liftA (norm_nonneg T₅)
        intro f
        change ‖(ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E6)
          ((E3 →L[ℝ] E6) →L[ℝ] Mat)
          ((E3 →L[ℝ] E6) →L[ℝ] E6) T₅) f‖ ≤ ‖T₅‖ * ‖f‖
        rw [ContinuousLinearMap.compL_apply]
        exact T₅.opNorm_comp_le f
      _ ≤ 3 := hT₅norm
  have hT₅liftKNorm : ‖T₅liftK‖ ≤ 3 := by
    calc
      ‖T₅liftK‖ ≤ ‖T₅liftA‖ := by
        apply ContinuousLinearMap.opNorm_le_bound T₅liftK (norm_nonneg T₅liftA)
        intro f
        change ‖(ContinuousLinearMap.compL ℝ (E3 →L[ℝ] E3)
          ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] Mat)
          ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) T₅liftA) f‖ ≤
            ‖T₅liftA‖ * ‖f‖
        rw [ContinuousLinearMap.compL_apply]
        exact T₅liftA.opNorm_comp_le f
      _ ≤ 3 := hT₅liftANorm

  have hQ₁norm : ‖Q₁‖ ≤ 10000 := by
    calc
      ‖Q₁‖ ≤ ‖Q‖ * ‖C‖ := Q.opNorm_comp_le C
      _ ≤ ‖Q‖ * 1 := mul_le_mul_of_nonneg_left hCnorm (norm_nonneg Q)
      _ ≤ 10000 * 1 := mul_le_mul_of_nonneg_right hQnorm (by norm_num)
      _ = 10000 := by norm_num
  have hQ₂norm : ‖Q₂‖ ≤ 10000 := by
    calc
      ‖Q₂‖ ≤ ‖T₂‖ * ‖Q₁‖ := T₂.opNorm_comp_le Q₁
      _ ≤ 1 * ‖Q₁‖ := mul_le_mul_of_nonneg_right hT₂norm (norm_nonneg Q₁)
      _ ≤ 1 * 10000 := mul_le_mul_of_nonneg_left hQ₁norm (by norm_num)
      _ = 10000 := by norm_num
  have hQ₃norm : ‖Q₃‖ ≤ 10000 := by
    calc
      ‖Q₃‖ ≤ ‖T₃lift‖ * ‖Q₂‖ := T₃lift.opNorm_comp_le Q₂
      _ ≤ 1 * ‖Q₂‖ := mul_le_mul_of_nonneg_right hT₃liftNorm (norm_nonneg Q₂)
      _ ≤ 1 * 10000 := mul_le_mul_of_nonneg_left hQ₂norm (by norm_num)
      _ = 10000 := by norm_num
  have hQ₄norm : ‖Q₄‖ ≤ 10000 := by
    calc
      ‖Q₄‖ ≤ ‖T₄liftK‖ * ‖Q₃‖ := T₄liftK.opNorm_comp_le Q₃
      _ ≤ 1 * ‖Q₃‖ := mul_le_mul_of_nonneg_right hT₄liftKNorm (norm_nonneg Q₃)
      _ ≤ 1 * 10000 := mul_le_mul_of_nonneg_left hQ₃norm (by norm_num)
      _ = 10000 := by norm_num

  have hBnorm : ‖B‖ ≤ 30000 := by
    calc
      ‖B‖ ≤ ‖T₅liftK‖ * ‖Q₄‖ := T₅liftK.opNorm_comp_le Q₄
      _ ≤ 3 * ‖Q₄‖ := mul_le_mul_of_nonneg_right hT₅liftKNorm (norm_nonneg Q₄)
      _ ≤ 3 * 10000 := mul_le_mul_of_nonneg_left hQ₄norm (by norm_num)
      _ = 30000 := by norm_num

  have hBeval (H K : E3 →L[ℝ] E3) (A G : E3 →L[ℝ] E6) :
      B H K A G = P (Q (C H) (C K) (D A) (D G)) := rfl

  refine ⟨B, hBnorm, ?_, ?_⟩
  · intro H K A G
    let h : Mat := fun i j => (H (EuclideanSpace.single j 1)) i
    let k : Mat := fun i j => (K (EuclideanSpace.single j 1)) i
    let d : First := fun a i j =>
      symmetricSixMatrix (A (EuclideanSpace.single a 1)) i j
    let e : First := fun a i j =>
      symmetricSixMatrix (G (EuclideanSpace.single a 1)) i j
    have hC_H : C H = h := by
      funext i j
      exact hCentry H i j
    have hC_K : C K = k := by
      funext i j
      exact hCentry K i j
    have hD_A : D A = d := by
      funext a i j
      exact hDentry A a i j
    have hD_G : D G = e := by
      funext a i j
      exact hDentry G a i j
    have hq : Q (C H) (C K) (D A) (D G) = deturckQuadratic h k d e := by
      ext i j
      simpa only [hC_H, hC_K, hD_A, hD_G] using
        hQentry (C H) (C K) (D A) (D G) i j
    rw [hBeval, hq]
    let m : Mat := deturckQuadratic h k d e
    rcases hPentry m with ⟨h00, h11, h22, h01, h02, h12⟩
    ext n
    fin_cases n
    · simpa [m] using h00
    · simpa [m] using h11
    · simpa [m] using h22
    · simpa [m] using h01
    · simpa [m] using h02
    · simpa [m] using h12
  · intro H A hHs i j
    let h : Mat := fun r s => (H (EuclideanSpace.single s 1)) r
    let d : First := fun a r s =>
      symmetricSixMatrix (A (EuclideanSpace.single a 1)) r s
    have hC_H : C H = h := by
      funext r s
      exact hCentry H r s
    have hD_A : D A = d := by
      funext a r s
      exact hDentry A a r s
    have hh : ∀ r s : Idx, h r s = h s r := by
      intro r s
      exact hHs r s
    have hd : ∀ a r s : Idx, d a r s = d a s r := by
      intro a r s
      simpa only [hD_A] using hDsymmetric A a r s
    let m : Mat := deturckQuadratic h h d d
    have hq : Q (C H) (C H) (D A) (D A) = m := by
      ext r s
      simpa only [hC_H, hD_A, m] using hQentry (C H) (C H) (D A) (D A) r s
    have hBdiag : B H H A A = P m := by
      rw [hBeval, hq]
    have hmSym : ∀ r s : Idx, m r s = m s r := by
      intro r s
      exact PoincareConjecture.ParallelImplementation.CoordinateDeTurckSymmetry.deturck_quadratic_symmetric
        h d hh hd r s
    have hroundtrip := hPsymmetric m hmSym
    calc
      symmetricSixMatrix (B H H A A) i j = m i j := by
        rw [hBdiag]
        exact congrArg (fun M : Mat => M i j) hroundtrip
      _ = deturckQuadratic h h d d i j := rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixCoordinateDeTurckNonlinearity
