import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LoweredDeTurckGauge
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LoweredGaugeJet
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual spatial differentiation of the lowered gauge separates second jets from inverse differentiation. -/
theorem lowered_gauge_field_derivative (G : E3 → (E3 →L[ℝ] E3))
    (hG : ContDiff ℝ 2 G) (x : E3) (c : ℝ) (hc : 0<c)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (r j : Fin 3) :
    let P := fun a : Fin 3 => fderiv ℝ G x (EuclideanSpace.single a 1);
    let C : Matrix (Fin 3) (Fin 3) ℝ := fun a b => ((G x).inverse (EuclideanSpace.single b 1)) a;
    let Q := fun a b m n : Fin 3 =>
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single b 1)) x
        (EuclideanSpace.single a 1) (EuclideanSpace.single n 1)) m;
    fderiv ℝ (fun y : E3 => loweredDeTurckGauge (G y)
      (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) j) x (EuclideanSpace.single r 1) =
      (1/2:ℝ)*(∑ p : Fin 3, ∑ q : Fin 3,
        C p q*(Q r p j q+Q r q j p-Q r j p q)) + loweredGaugeJet (G x) P r j :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  classical
  let e : Fin 3 → E3 := fun a => EuclideanSpace.single a 1
  have hGx : ContDiffAt ℝ 2 G x := hG.contDiffAt
  have hG' : DifferentiableAt ℝ (fderiv ℝ G) x :=
    (hGx.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hInvCD : ContDiffAt ℝ ∞
      (fun B : E3 →L[ℝ] E3 => B.inverse) (G x) :=
    (coercive_inverse_differential (G x) c hc hpos).1
  have hInv : HasFDerivAt (fun B : E3 →L[ℝ] E3 => B.inverse)
      (fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) (G x)) (G x) :=
    (hInvCD.differentiableAt (by norm_num)).hasFDerivAt
  have hInvField : HasFDerivAt (fun y : E3 => (G y).inverse)
      ((fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) (G x)).comp
        (fderiv ℝ G x)) x :=
    hInv.comp x (hGx.differentiableAt (by norm_num)).hasFDerivAt
  let dInv : Fin 3 → Fin 3 → E3 →L[ℝ] ℝ := fun p q =>
    (EuclideanSpace.proj (𝕜 := ℝ) p).comp
      (((fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) (G x)).comp
        (fderiv ℝ G x)).flip (e q))
  let dP : Fin 3 → Fin 3 → Fin 3 → E3 →L[ℝ] ℝ := fun a b s =>
    (EuclideanSpace.proj (𝕜 := ℝ) s).comp
      (((fderiv ℝ (fderiv ℝ G) x).flip (e a)).flip (e b))
  have hInvCoord : ∀ p q : Fin 3,
      HasFDerivAt (fun y : E3 => ((G y).inverse (e q)) p)
        (dInv p q) x := by
    intro p q
    have h := hInvField.clm_apply (hasFDerivAt_const (e q) x)
    simpa [dInv, e, Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) p).hasFDerivAt.comp x h
  have hPField : ∀ a : Fin 3,
      HasFDerivAt (fun y : E3 => (fderiv ℝ G y) (e a))
        ((fderiv ℝ (fderiv ℝ G) x).flip (e a)) x := by
    intro a
    simpa using hG'.hasFDerivAt.clm_apply (hasFDerivAt_const (e a) x)
  have hPCoord : ∀ a b s : Fin 3,
      HasFDerivAt
        (fun y : E3 => ((fderiv ℝ G y) (e a) (e b)) s)
        (dP a b s) x := by
    intro a b s
    have h := (hPField a).clm_apply (hasFDerivAt_const (e b) x)
    simpa [dP, e, Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) s).hasFDerivAt.comp x h
  have hterm : ∀ p q : Fin 3,
      HasFDerivAt
        (fun y : E3 =>
          ((G y).inverse (e q)) p *
            (((fderiv ℝ G y) (e p) (e q)) j +
              ((fderiv ℝ G y) (e q) (e p)) j -
                ((fderiv ℝ G y) (e j) (e q)) p))
        (((G x).inverse (e q) p) •
            (dP p q j + dP q p j - dP j q p) +
          (((fderiv ℝ G x) (e p) (e q)) j +
              ((fderiv ℝ G x) (e q) (e p)) j -
                ((fderiv ℝ G x) (e j) (e q)) p) • dInv p q) x := by
    intro p q
    have hbracket := (hPCoord p q j).add (hPCoord q p j) |>.sub (hPCoord j q p)
    have hprod := (hInvCoord p q).mul hbracket
    convert hprod using 1
    all_goals try apply Subsingleton.elim
    all_goals try rfl
    all_goals
      ext v <;> simp [dInv, dP, e, Function.comp_def]
  have hsumq (p : Fin 3) :=
    HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
      (fun q _ => hterm p q)
  have hsum := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
    (fun p _ => hsumq p)
  have hhalf := hsum.const_smul (1 / 2 : ℝ)
  have heval := congrArg (fun D : E3 →L[ℝ] ℝ => D (e r)) hhalf.fderiv
  have hfun :
      (1 / 2 : ℝ) •
          (∑ p : Fin 3, ∑ q : Fin 3, fun y : E3 =>
            ((G y).inverse (e q)) p *
              (((fderiv ℝ G y) (e p) (e q)) j +
                ((fderiv ℝ G y) (e q) (e p)) j -
                  ((fderiv ℝ G y) (e j) (e q)) p)) =
        (fun y : E3 => (1 / 2 : ℝ) * ∑ p : Fin 3, ∑ q : Fin 3,
          ((G y).inverse (e q)) p *
            (((fderiv ℝ G y) (e p) (e q)) j +
              ((fderiv ℝ G y) (e q) (e p)) j -
                ((fderiv ℝ G y) (e j) (e q)) p)) := by
    funext y
    simp [smul_eq_mul, Finset.sum_apply]
  rw [hfun] at heval
  have hP_eval : ∀ a b s : Fin 3,
      ((fderiv ℝ (fun y : E3 =>
        (fderiv ℝ G y) (EuclideanSpace.single a 1)) x
          (EuclideanSpace.single r 1)) (EuclideanSpace.single b 1)) s =
        ((fderiv ℝ (fderiv ℝ G) x) (EuclideanSpace.single r 1)
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) s := by
    intro a b s
    have hB : DifferentiableAt ℝ
        (fun y : E3 => (fderiv ℝ G y) (e a)) x :=
      (hPField a).differentiableAt
    have h := fderiv_clm_apply hB (differentiableAt_const (c := e b) (x := x))
    have hvec0 := (hPField a).clm_apply (hasFDerivAt_const (e b) x)
    have hvecd := hvec0.fderiv
    have hvec : HasFDerivAt (fun y : E3 =>
        ((fderiv ℝ G y) (e a)) (e b))
        (fderiv ℝ (fun y : E3 =>
          ((fderiv ℝ G y) (e a)) (e b)) x) x := by
      rw [hvecd]
      exact hvec0
    have hcoord : fderiv ℝ (fun y : E3 =>
        (((fderiv ℝ G y) (e a)) (e b)) s) x (e r) =
        (fderiv ℝ (fun y : E3 =>
          ((fderiv ℝ G y) (e a)) (e b)) x (e r)) s := by
      have hs := ((EuclideanSpace.proj (𝕜 := ℝ) s).hasFDerivAt.comp x hvec).fderiv
      have hs' := congrArg (fun L : E3 →L[ℝ] ℝ => L (e r)) hs
      simpa [Function.comp_def, EuclideanSpace.coe_proj,
        ContinuousLinearMap.comp_apply] using hs'
    have hv : fderiv ℝ (fun y : E3 =>
        ((fderiv ℝ G y) (e a)) (e b)) x (e r) =
        (fderiv ℝ (fun y : E3 => (fderiv ℝ G y) (e a)) x (e r)) (e b) := by
      simpa using congrArg (fun L => L (e r)) h
    calc
      ((fderiv ℝ (fun y : E3 => (fderiv ℝ G y)
          (EuclideanSpace.single a 1)) x (EuclideanSpace.single r 1))
            (EuclideanSpace.single b 1)) s =
          (fderiv ℝ (fun y : E3 =>
            (((fderiv ℝ G y) (e a)) (e b)) s) x (e r)) := by
            calc
              _ = (fderiv ℝ (fun y : E3 =>
                ((fderiv ℝ G y) (e a)) (e b)) x (e r)) s := by
                  simpa [e] using congrArg (fun v : E3 => v s) hv.symm
              _ = _ := hcoord.symm
      _ = ((fderiv ℝ (fderiv ℝ G) x) (EuclideanSpace.single r 1)
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) s := by
            have h' := congrArg (fun L : E3 →L[ℝ] ℝ => L (e r))
              (hPCoord a b s).fderiv
            simpa [dP, e, Function.comp_def, EuclideanSpace.coe_proj,
              ContinuousLinearMap.comp_apply] using h'
  have hinv := (coercive_inverse_differential (G x) c hc hpos).2
  convert heval using 1
  all_goals try apply Subsingleton.elim
  all_goals try rfl
  all_goals
    simp [smul_eq_mul, dInv, dP, e, Function.comp_def,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  simp only [loweredGaugeJet]
  try simp_rw [hP_eval]
  try simp_rw [hinv]
  simp_rw [Finset.sum_add_distrib]
  simp [mul_comm] <;> ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
