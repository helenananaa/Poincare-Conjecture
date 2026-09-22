import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseQuadraticRemainder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PrincipalPartDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Smooth dependence of the actual displayed Christoffel expression on metric and first jets. -/
theorem coordinate_christoffel_smooth (A : E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (P : Fin 3 → E3 →L[ℝ] E3) (k i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
      coordinateChristoffel q.1 q.2 k i j) (A,P) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hInv : ContDiffAt ℝ ∞ (fun B : E3 →L[ℝ] E3 => B.inverse) A :=
    (coercive_inverse_differential A c hc hA).1
  have hInv' : ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) => q.1.inverse) (A, P) :=
    hInv.comp (A, P) contDiffAt_fst
  have hcoord : ∀ (r l s : Fin 3),
      ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          (q.2 r (EuclideanSpace.single l 1)) s) (A, P) := by
    intro r l s
    fun_prop
  have hterm : ∀ l : Fin 3,
      ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          q.1.inverse (EuclideanSpace.single l 1) k *
            ((q.2 i (EuclideanSpace.single l 1)) j +
              (q.2 j (EuclideanSpace.single l 1)) i -
                (q.2 l (EuclideanSpace.single j 1)) i)) (A, P) := by
    intro l
    have hinv_l : ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          q.1.inverse (EuclideanSpace.single l 1) k) (A, P) := by
      simpa [Function.comp_def, EuclideanSpace.coe_proj] using
        ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt.comp (A, P)
          (hInv'.clm_apply contDiffAt_const))
    exact hinv_l.mul ((hcoord i l j).add (hcoord j l i) |>.sub (hcoord l j i))
  have hsum : ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        ∑ l : Fin 3,
          q.1.inverse (EuclideanSpace.single l 1) k *
            ((q.2 i (EuclideanSpace.single l 1)) j +
              (q.2 j (EuclideanSpace.single l 1)) i -
                (q.2 l (EuclideanSpace.single j 1)) i)) (A, P) := by
    simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun l _ => hterm l))
  simpa [coordinateChristoffel] using hsum.const_smul (1 / 2 : ℝ)
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
