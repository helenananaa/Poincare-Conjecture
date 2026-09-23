import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
def backgroundConnectionContraction (A : E3 →L[ℝ] E3) (T : T3) : E3 :=
  WithLp.toLp 2 (fun k : Fin 3 => ∑ i : Fin 3, ∑ j : Fin 3,
    (A.inverse (EuclideanSpace.single j 1)) i * T k i j)

/-- **Math.** background connection contraction smooth. -/
theorem background_connection_contraction_smooth (A : E3 →L[ℝ] E3) (T : T3) (c : ℝ) (hc : 0 < c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) :
    ContDiffAt ℝ ∞ (fun z : (E3 →L[ℝ] E3) × T3 =>
      backgroundConnectionContraction z.1 z.2) (A,T) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  apply contDiffAt_euclidean.mpr
  intro k
  change ContDiffAt ℝ ∞
    (fun z : (E3 →L[ℝ] E3) × T3 =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        (z.1.inverse (EuclideanSpace.single j 1)) i * z.2 k i j) (A, T)
  have hInv : ContDiffAt ℝ ∞ (fun B : E3 →L[ℝ] E3 => B.inverse) A :=
    (coercive_inverse_differential A c hc hA).1
  have hInv' : ContDiffAt ℝ ∞
      (fun z : (E3 →L[ℝ] E3) × T3 => z.1.inverse) (A, T) :=
    hInv.comp (A, T) contDiffAt_fst
  have hterm : ∀ i j : Fin 3,
      ContDiffAt ℝ ∞
        (fun z : (E3 →L[ℝ] E3) × T3 =>
          (z.1.inverse (EuclideanSpace.single j 1)) i * z.2 k i j) (A, T) := by
    intro i j
    have hinv : ContDiffAt ℝ ∞
        (fun z : (E3 →L[ℝ] E3) × T3 =>
          (z.1.inverse (EuclideanSpace.single j 1)) i) (A, T) := by
      simpa [Function.comp_def, EuclideanSpace.coe_proj] using
        ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp (A, T)
          (hInv'.clm_apply contDiffAt_const))
    have hT : ContDiffAt ℝ ∞
        (fun z : (E3 →L[ℝ] E3) × T3 => z.2 k i j) (A, T) := by
      fun_prop
    exact hinv.mul hT
  have hsumj : ∀ i : Fin 3,
      ContDiffAt ℝ ∞
        (fun z : (E3 →L[ℝ] E3) × T3 =>
          ∑ j : Fin 3,
            (z.1.inverse (EuclideanSpace.single j 1)) i * z.2 k i j) (A, T) := by
    intro i
    simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _ => hterm i j))
  simpa [backgroundConnectionContraction] using
    (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun i _ => hsumj i))
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
