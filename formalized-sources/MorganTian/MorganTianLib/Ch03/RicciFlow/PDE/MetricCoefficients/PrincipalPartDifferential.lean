import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PrincipalBilinear
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Smoothness and exact linearization of the quasilinear principal algebra map. -/
theorem inverse_metric_principal_differential (A : E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0<c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (Q : Fin 3 → Fin 3 → E6) :
    let P := fun p : (E3 →L[ℝ] E3) × (Fin 3 → Fin 3 → E6) =>
      ∑ i : Fin 3, ∑ j : Fin 3, (p.1.inverse (EuclideanSpace.single j 1)) i • p.2 i j
    ContDiffAt ℝ ∞ P (A,Q) ∧ ∀ (H : E3 →L[ℝ] E3) (R : Fin 3 → Fin 3 → E6),
      fderiv ℝ P (A,Q) (H,R) = ∑ i : Fin 3, ∑ j : Fin 3,
        (((-(A.inverse.comp (H.comp A.inverse))) (EuclideanSpace.single j 1)) i • Q i j +
          (A.inverse (EuclideanSpace.single j 1)) i • R i j) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp
  obtain ⟨B, hB⟩ := principal_contraction_bilinear
  have hInv : ContDiffAt ℝ ∞
      (fun C : E3 →L[ℝ] E3 => C.inverse) A :=
    (coercive_inverse_differential A c hc hA).1
  have hInvF : HasFDerivAt
      (fun C : E3 →L[ℝ] E3 => C.inverse)
      (fderiv ℝ (fun C : E3 →L[ℝ] E3 => C.inverse) A) A :=
    (hInv.differentiableAt (by norm_num)).hasFDerivAt
  have hInvProd : HasFDerivAt
      (fun p : (E3 →L[ℝ] E3) × (Fin 3 → Fin 3 → E6) => p.1.inverse)
      ((fderiv ℝ (fun C : E3 →L[ℝ] E3 => C.inverse) A).comp
        (ContinuousLinearMap.fst ℝ (E3 →L[ℝ] E3) (Fin 3 → Fin 3 → E6)))
      (A, Q) := by
    exact hInvF.comp (A, Q) (hasFDerivAt_fst (𝕜 := ℝ))
  have hP : ContDiffAt ℝ ∞
      (fun p : (E3 →L[ℝ] E3) × (Fin 3 → Fin 3 → E6) =>
        B p.1.inverse p.2) (A, Q) := by
    have hBinv : ContDiffAt ℝ ∞
        (fun C : E3 →L[ℝ] E3 => B C.inverse) A :=
      B.contDiff.contDiffAt.comp A hInv
    apply (hBinv.comp (A, Q) contDiffAt_fst).clm_apply
    exact contDiffAt_snd
  constructor
  · simpa [hB] using hP
  · intro H R
    have hfirst : HasFDerivAt
        (fun p : (E3 →L[ℝ] E3) × (Fin 3 → Fin 3 → E6) =>
          B p.1.inverse p.2)
        ((B A.inverse).comp
            (ContinuousLinearMap.snd ℝ (E3 →L[ℝ] E3)
              (Fin 3 → Fin 3 → E6)) +
          (B.comp
            ((fderiv ℝ (fun C : E3 →L[ℝ] E3 => C.inverse) A).comp
              (ContinuousLinearMap.fst ℝ (E3 →L[ℝ] E3)
                (Fin 3 → Fin 3 → E6)))).flip Q) (A, Q) := by
      have hBInv : HasFDerivAt
          (fun p : (E3 →L[ℝ] E3) × (Fin 3 → Fin 3 → E6) => B p.1.inverse)
          (B.comp
            ((fderiv ℝ (fun C : E3 →L[ℝ] E3 => C.inverse) A).comp
              (ContinuousLinearMap.fst ℝ (E3 →L[ℝ] E3)
                (Fin 3 → Fin 3 → E6)))) (A, Q) := by
        exact (B.hasFDerivAt.comp (A, Q) hInvProd)
      exact hBInv.clm_apply (hasFDerivAt_snd (𝕜 := ℝ))
    have hderiv := hfirst.fderiv
    have hinv := (coercive_inverse_differential A c hc hA).2 H
    have hval := congrArg (fun L => L (H, R)) hderiv
    change (fderiv ℝ
        (fun p : (E3 →L[ℝ] E3) × (Fin 3 → Fin 3 → E6) =>
          B p.1.inverse p.2) (A, Q)) (H, R) =
      B A.inverse R + B ((fderiv ℝ (fun C : E3 →L[ℝ] E3 => C.inverse) A) H) Q at hval
    rw [hinv] at hval
    have hval' :
        (fderiv ℝ
          (fun p : (E3 →L[ℝ] E3) × (Fin 3 → Fin 3 → E6) =>
            B p.1.inverse p.2) (A, Q)) (H, R) =
          (∑ i : Fin 3, ∑ j : Fin 3,
            (A.inverse (EuclideanSpace.single j 1)) i • R i j) +
          ∑ i : Fin 3, ∑ j : Fin 3,
            ((-(A.inverse.comp (H.comp A.inverse)))
              (EuclideanSpace.single j 1)) i • Q i j := by
      simpa only [hB, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
        Finset.sum_neg_distrib] using hval
    have hfun :
        (fun p : (E3 →L[ℝ] E3) × (Fin 3 → Fin 3 → E6) =>
          B p.1.inverse p.2) =
        (fun p : (E3 →L[ℝ] E3) × (Fin 3 → Fin 3 → E6) =>
          ∑ i : Fin 3, ∑ j : Fin 3,
            (p.1.inverse (EuclideanSpace.single j 1)) i • p.2 i j) := by
      funext p
      exact hB p.1.inverse p.2
    rw [← hfun]
    calc
      _ = (∑ i : Fin 3, ∑ j : Fin 3,
          (A.inverse (EuclideanSpace.single j 1)) i • R i j) +
          ∑ i : Fin 3, ∑ j : Fin 3,
            ((-(A.inverse.comp (H.comp A.inverse)))
              (EuclideanSpace.single j 1)) i • Q i j := hval'
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          (((-(A.inverse.comp (H.comp A.inverse)))
              (EuclideanSpace.single j 1)) i • Q i j +
            (A.inverse (EuclideanSpace.single j 1)) i • R i j) := by
        simp only [Finset.sum_add_distrib]
        ac_rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
