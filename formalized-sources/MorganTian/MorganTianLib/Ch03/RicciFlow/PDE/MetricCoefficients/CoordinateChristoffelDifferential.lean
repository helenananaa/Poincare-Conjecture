import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateMetricCompatibility
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffelSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricInverseBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual first derivative of the Christoffel formula in both coefficient and first-jet variables. -/
theorem coordinate_christoffel_differential (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (k i j : Fin 3) (H : E3 →L[ℝ] E3) (R : Fin 3 → E3 →L[ℝ] E3) :
    fderiv ℝ (fun p : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
      coordinateChristoffel p.1 p.2 k i j) (A,P) (H,R) =
      (1/2:ℝ)*∑ l : Fin 3,
        (((-(A.inverse.comp (H.comp A.inverse))) (EuclideanSpace.single l 1)) k *
          ((P i (EuclideanSpace.single l 1)) j+(P j (EuclideanSpace.single l 1)) i-
            (P l (EuclideanSpace.single j 1)) i) +
        (A.inverse (EuclideanSpace.single l 1)) k *
          ((R i (EuclideanSpace.single l 1)) j+(R j (EuclideanSpace.single l 1)) i-
            (R l (EuclideanSpace.single j 1)) i)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hInvCD : ContDiffAt ℝ ∞ (fun B : E3 →L[ℝ] E3 => B.inverse) A :=
    (coercive_inverse_differential A c hc hA).1
  have hInv : HasFDerivAt (fun B : E3 →L[ℝ] E3 => B.inverse)
      (fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) A) A :=
    (hInvCD.differentiableAt (by norm_num)).hasFDerivAt
  have hInvProd : HasFDerivAt
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) => q.1.inverse)
      ((fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) A).comp
        (ContinuousLinearMap.fst ℝ (E3 →L[ℝ] E3) (Fin 3 → E3 →L[ℝ] E3))) (A, P) := by
    exact hInv.comp (A, P) (hasFDerivAt_fst (𝕜 := ℝ))
  let dInv : Fin 3 →
      ((E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)) →L[ℝ] ℝ := fun l =>
    (EuclideanSpace.proj (𝕜 := ℝ) k).comp
      (((fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) A).comp
        (ContinuousLinearMap.fst ℝ (E3 →L[ℝ] E3)
          (Fin 3 → E3 →L[ℝ] E3))).flip (EuclideanSpace.single l (1 : ℝ)))
  let dP : Fin 3 → Fin 3 → Fin 3 →
      ((E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)) →L[ℝ] ℝ := fun r s l =>
    (EuclideanSpace.proj (𝕜 := ℝ) s).comp
      (((ContinuousLinearMap.proj (R := ℝ) r).comp
        (ContinuousLinearMap.snd ℝ (E3 →L[ℝ] E3)
          (Fin 3 → E3 →L[ℝ] E3))).flip (EuclideanSpace.single l (1 : ℝ)))
  have hInvCoord : ∀ l : Fin 3,
      HasFDerivAt
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          (q.1.inverse (EuclideanSpace.single l (1 : ℝ))) k)
        (dInv l) (A, P) := by
    intro l
    have h := hInvProd.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single l (1 : ℝ)) (A, P))
    have h' : HasFDerivAt
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          q.1.inverse (EuclideanSpace.single l (1 : ℝ)))
        (((fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) A).comp
          (ContinuousLinearMap.fst ℝ (E3 →L[ℝ] E3) (Fin 3 → E3 →L[ℝ] E3))).flip
          (EuclideanSpace.single l (1 : ℝ))) (A, P) := by
      simpa using h
    simpa [dInv, Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp (A, P) h'
  have hPCoord : ∀ (r s l : Fin 3),
      HasFDerivAt
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          (q.2 r (EuclideanSpace.single l (1 : ℝ))) s)
        (dP r s l) (A, P) := by
    intro r s l
    have hmap : HasFDerivAt
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) => q.2 r)
        ((ContinuousLinearMap.proj r).comp
          (ContinuousLinearMap.snd ℝ (E3 →L[ℝ] E3)
            (Fin 3 → E3 →L[ℝ] E3))) (A, P) := by
      exact (ContinuousLinearMap.proj (R := ℝ) r).hasFDerivAt.comp (A, P)
        (hasFDerivAt_snd (𝕜 := ℝ))
    have h := hmap.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single l (1 : ℝ)) (A, P))
    have h' : HasFDerivAt
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          q.2 r (EuclideanSpace.single l (1 : ℝ)))
        ((((ContinuousLinearMap.proj (R := ℝ) r).comp
          (ContinuousLinearMap.snd ℝ (E3 →L[ℝ] E3)
            (Fin 3 → E3 →L[ℝ] E3))).flip (EuclideanSpace.single l (1 : ℝ)))) (A, P) := by
      simpa using h
    simpa [dP, Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) s).hasFDerivAt.comp (A, P) h'
  have hterm : ∀ l : Fin 3,
      HasFDerivAt
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          (q.1.inverse (EuclideanSpace.single l (1 : ℝ))) k *
            ((q.2 i (EuclideanSpace.single l (1 : ℝ))) j +
              (q.2 j (EuclideanSpace.single l (1 : ℝ))) i -
                (q.2 l (EuclideanSpace.single j (1 : ℝ))) i))
        ((A.inverse (EuclideanSpace.single l (1 : ℝ))) k •
            (dP i j l + dP j i l - dP l i j) +
          ((P i (EuclideanSpace.single l (1 : ℝ))) j +
              (P j (EuclideanSpace.single l (1 : ℝ))) i -
                (P l (EuclideanSpace.single j (1 : ℝ))) i) • dInv l) (A, P) := by
    intro l
    have hbracket := (hPCoord i j l).add (hPCoord j i l) |>.sub (hPCoord l i j)
    have hprod := (hInvCoord l).mul hbracket
    convert hprod using 1
    all_goals try apply Subsingleton.elim
    all_goals try rfl
    all_goals
      ext q <;> simp [dInv, dP, Function.comp_def]
  have hsum := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
    (fun l _ => hterm l)
  have hhalf := hsum.const_smul (1 / 2 : ℝ)
  have hinv := (coercive_inverse_differential A c hc hA).2
  have heval := congrArg (fun D : ((E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)) →L[ℝ] ℝ => D (H,R)) hhalf.fderiv
  have hfun :
      (1 / 2 : ℝ) •
          (∑ l : Fin 3, fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
            (q.1.inverse (EuclideanSpace.single l 1)) k *
              ((q.2 i (EuclideanSpace.single l 1)) j +
                (q.2 j (EuclideanSpace.single l 1)) i -
                  (q.2 l (EuclideanSpace.single j 1)) i)) =
        (fun q => (1 / 2 : ℝ) * ∑ l : Fin 3,
          (q.1.inverse (EuclideanSpace.single l 1)) k *
            ((q.2 i (EuclideanSpace.single l 1)) j +
              (q.2 j (EuclideanSpace.single l 1)) i -
                (q.2 l (EuclideanSpace.single j 1)) i)) := by
    funext q
    simp [smul_eq_mul]
  rw [hfun] at heval
  simp only [coordinateChristoffel]
  convert heval using 1
  all_goals try apply Subsingleton.elim
  all_goals try rfl
  all_goals
    simp [smul_eq_mul, hinv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, dInv, dP]
  all_goals
    apply Finset.sum_congr rfl
    intro x hx
    ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
