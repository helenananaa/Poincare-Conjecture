import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BackgroundContractionDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateLieMetricLowering
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
def backgroundContractionJet (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (T : T3) (R : Fin 3 → T3) (r k : Fin 3) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, (
    ((-(A.inverse.comp ((P r).comp A.inverse))) (EuclideanSpace.single b 1)) a * T k a b +
      (A.inverse (EuclideanSpace.single b 1)) a * R r k a b)

def backgroundLieCorrection (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (T : T3) (R : Fin 3 → T3) (i j : Fin 3) : ℝ :=
  (∑ k : Fin 3, (backgroundConnectionContraction A T) k * (P k (EuclideanSpace.single j 1)) i) +
    ∑ k : Fin 3, ((A (EuclideanSpace.single k 1)) j * backgroundContractionJet A P T R i k +
      (A (EuclideanSpace.single k 1)) i * backgroundContractionJet A P T R j k)

/-- **Math.** background lie first order. -/
theorem background_lie_first_order (G : E3 → (E3 →L[ℝ] E3)) (T : E3 → T3) (x : E3)
    (hG : DifferentiableAt ℝ G x) (hT : DifferentiableAt ℝ T x)
    (c : ℝ) (hc : 0<c) (hpos : ∀ w : E3, c*‖w‖^2 ≤ inner ℝ (G x w) w) (i j : Fin 3) :
    let P := fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1);
    let R := fun r k a b : Fin 3 => fderiv ℝ (fun y => T y k a b) x (EuclideanSpace.single r 1);
    coordinateLieMetricExpr G (fun y => backgroundConnectionContraction (G y) (T y)) x i j =
      backgroundLieCorrection (G x) P (T x) R i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let e : Fin 3 → E3 := fun k => EuclideanSpace.single k 1
  let P : Fin 3 → E3 →L[ℝ] E3 := fun r =>
    fderiv ℝ G x (EuclideanSpace.single r 1)
  let R : Fin 3 → T3 := fun r k a b =>
    fderiv ℝ (fun y => T y k a b) x (EuclideanSpace.single r 1)
  have hexpand (v : E3) : v = ∑ k : Fin 3, v k • e k := by
    symm
    simpa [e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  have hGexpand :
      (fderiv ℝ G x (backgroundConnectionContraction (G x) (T x)) (e j)) i =
        ∑ k : Fin 3, backgroundConnectionContraction (G x) (T x) k *
          (fderiv ℝ G x (e k) (e j)) i := by
    conv_lhs => rw [hexpand (backgroundConnectionContraction (G x) (T x))]
    simp [e, map_sum, map_smul, smul_eq_mul]
  have hderiv (r k : Fin 3) :
      (fderiv ℝ (fun y : E3 => backgroundConnectionContraction (G y) (T y)) x
        (e r)) k = backgroundContractionJet (G x) P (T x) R r k := by
    rw [background_contraction_derivative G T x (e r) hG hT c hc hpos k]
    rfl
  have hderiv' (r k : Fin 3) :
      (fderiv ℝ (fun y : E3 => backgroundConnectionContraction (G y) (T y)) x
        (EuclideanSpace.single r 1)) k = backgroundContractionJet (G x) P (T x) R r k := by
    simpa [e] using hderiv r k
  dsimp [coordinateLieMetricExpr, backgroundLieCorrection]
  rw [hGexpand]
  simp_rw [hderiv']
  rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
