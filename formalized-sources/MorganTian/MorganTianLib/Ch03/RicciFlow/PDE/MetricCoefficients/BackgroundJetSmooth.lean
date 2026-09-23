import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BackgroundLieCorrection
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "JBg" => J3 × (T3 × (Fin 3 → T3))
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** background jet smooth. -/
theorem background_jet_smooth (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3) (T : T3) (R : Fin 3 → T3)
    (c : ℝ) (hc : 0 < c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) (r k : Fin 3) :
    ContDiffAt ℝ ∞ (fun q : JBg => backgroundContractionJet q.1.1 q.1.2 q.2.1 q.2.2 r k) ((A,P),(T,R)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hInv : ContDiffAt ℝ ∞
      (fun B : E3 →L[ℝ] E3 => B.inverse) A :=
    (coercive_inverse_differential A c hc hA).1
  have hInv' : ContDiffAt ℝ ∞
      (fun q : JBg => q.1.1.inverse) ((A, P), (T, R)) :=
    hInv.comp ((A, P), (T, R)) (contDiffAt_fst.comp _ contDiffAt_fst)
  have hP : ∀ s : Fin 3, ContDiffAt ℝ ∞
      (fun q : JBg => q.1.2 s) ((A, P), (T, R)) := by
    intro s
    fun_prop
  have hJetComp : ContDiffAt ℝ ∞
      (fun q : JBg => q.1.1.inverse.comp ((q.1.2 r).comp q.1.1.inverse))
      ((A, P), (T, R)) :=
    hInv'.clm_comp ((hP r).clm_comp hInv')
  have hTcoord : ∀ (a b : Fin 3), ContDiffAt ℝ ∞
      (fun q : JBg => q.2.1 k a b) ((A, P), (T, R)) := by
    intro a b
    fun_prop
  have hRcoord : ∀ (a b : Fin 3), ContDiffAt ℝ ∞
      (fun q : JBg => q.2.2 r k a b) ((A, P), (T, R)) := by
    intro a b
    fun_prop
  have hterm : ∀ a b : Fin 3, ContDiffAt ℝ ∞
      (fun q : JBg =>
        (-(q.1.1.inverse.comp ((q.1.2 r).comp q.1.1.inverse))
          (EuclideanSpace.single b 1)) a * q.2.1 k a b +
        (q.1.1.inverse (EuclideanSpace.single b 1)) a * q.2.2 r k a b)
      ((A, P), (T, R)) := by
    intro a b
    have hfirst : ContDiffAt ℝ ∞
        (fun q : JBg =>
          (-(q.1.1.inverse.comp ((q.1.2 r).comp q.1.1.inverse))
            (EuclideanSpace.single b 1)) a) ((A, P), (T, R)) := by
      simpa [Function.comp_def, EuclideanSpace.coe_proj] using
        ((EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.contDiffAt.comp
          ((A, P), (T, R))
          ((hJetComp.neg).clm_apply contDiffAt_const))
    have hinv : ContDiffAt ℝ ∞
        (fun q : JBg => (q.1.1.inverse (EuclideanSpace.single b 1)) a)
        ((A, P), (T, R)) := by
      simpa [Function.comp_def, EuclideanSpace.coe_proj] using
        ((EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.contDiffAt.comp
          ((A, P), (T, R)) (hInv'.clm_apply contDiffAt_const))
    exact (hfirst.mul (hTcoord a b)).add (hinv.mul (hRcoord a b))
  have hsumB : ∀ a : Fin 3, ContDiffAt ℝ ∞
      (fun q : JBg =>
        ∑ b : Fin 3,
          ((-(q.1.1.inverse.comp ((q.1.2 r).comp q.1.1.inverse))
              (EuclideanSpace.single b 1)) a * q.2.1 k a b +
            (q.1.1.inverse (EuclideanSpace.single b 1)) a * q.2.2 r k a b))
      ((A, P), (T, R)) := by
    intro a
    simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun b _ => hterm a b))
  have hsum : ContDiffAt ℝ ∞
      (fun q : JBg =>
        ∑ a : Fin 3, ∑ b : Fin 3,
          ((-(q.1.1.inverse.comp ((q.1.2 r).comp q.1.1.inverse))
              (EuclideanSpace.single b 1)) a * q.2.1 k a b +
            (q.1.1.inverse (EuclideanSpace.single b 1)) a * q.2.2 r k a b))
      ((A, P), (T, R)) := by
    simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun a _ => hsumB a))
  simpa [backgroundContractionJet] using hsum
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
