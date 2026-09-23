import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LoweredGaugeJet
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** lowered gauge jet smooth. -/
theorem lowered_gauge_jet_smooth (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0 < c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (r j : Fin 3) :
    ContDiffAt ℝ ∞ (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
      loweredGaugeJet q.1 q.2 r j) (A,P) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hInv : ContDiffAt ℝ ∞
      (fun B : E3 →L[ℝ] E3 => B.inverse) A :=
    (coercive_inverse_differential A c hc hA).1
  have hInv' : ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) => q.1.inverse) (A, P) :=
    hInv.comp (A, P) contDiffAt_fst
  have hP : ∀ s : Fin 3, ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) => q.2 s) (A, P) := by
    intro s
    fun_prop
  have hJetComp : ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        q.1.inverse.comp ((q.2 r).comp q.1.inverse)) (A, P) :=
    hInv'.clm_comp ((hP r).clm_comp hInv')
  have hcoord : ∀ (s l t : Fin 3), ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        (q.2 s (EuclideanSpace.single l 1)) t) (A, P) := by
    intro s l t
    fun_prop
  have hterm : ∀ p q : Fin 3, ContDiffAt ℝ ∞
      (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        ((-(z.1.inverse.comp ((z.2 r).comp z.1.inverse)))
          (EuclideanSpace.single q 1)) p *
          (z.2 p (EuclideanSpace.single q 1) j +
            z.2 q (EuclideanSpace.single p 1) j -
              z.2 j (EuclideanSpace.single q 1) p)) (A, P) := by
    intro p q
    have hfirst : ContDiffAt ℝ ∞
        (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          ((-(z.1.inverse.comp ((z.2 r).comp z.1.inverse)))
            (EuclideanSpace.single q 1)) p) (A, P) := by
      simpa [Function.comp_def, EuclideanSpace.coe_proj] using
        ((EuclideanSpace.proj (𝕜 := ℝ) p).contDiff.contDiffAt.comp (A, P)
          (((hJetComp.neg).clm_apply contDiffAt_const)))
    exact hfirst.mul ((hcoord p q j).add (hcoord q p j) |>.sub (hcoord j q p))
  have hsumq : ∀ p : Fin 3, ContDiffAt ℝ ∞
      (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        ∑ q : Fin 3,
          ((-(z.1.inverse.comp ((z.2 r).comp z.1.inverse)))
            (EuclideanSpace.single q 1)) p *
            (z.2 p (EuclideanSpace.single q 1) j +
              z.2 q (EuclideanSpace.single p 1) j -
                z.2 j (EuclideanSpace.single q 1) p)) (A, P) := by
    intro p
    simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun q _ => hterm p q))
  have hsum : ContDiffAt ℝ ∞
      (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        ∑ p : Fin 3, ∑ q : Fin 3,
          ((-(z.1.inverse.comp ((z.2 r).comp z.1.inverse)))
            (EuclideanSpace.single q 1)) p *
            (z.2 p (EuclideanSpace.single q 1) j +
              z.2 q (EuclideanSpace.single p 1) j -
                z.2 j (EuclideanSpace.single q 1) p)) (A, P) := by
    simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun p _ => hsumq p))
  simpa [loweredGaugeJet] using hsum.const_smul (1 / 2 : ℝ)
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
