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
/-- Actual C2 metric Hessians have both mixed-partial and self-adjoint symmetries. -/
theorem metric_second_jets_symmetric (G : E3 → (E3 →L[ℝ] E3))
    (hG : ContDiff ℝ 2 G)
    (hsym : ∀ y v w : E3, inner ℝ (G y v) w=inner ℝ v (G y w)) (x : E3) :
    let Q := fun r s : Fin 3 => fderiv ℝ (fun y : E3 =>
      fderiv ℝ G y (EuclideanSpace.single s 1)) x (EuclideanSpace.single r 1)
    (∀ r s : Fin 3, Q r s=Q s r) ∧
      ∀ r s : Fin 3, ∀ v w : E3, inner ℝ (Q r s v) w=inner ℝ v (Q r s w) :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  have hGx : ContDiffAt ℝ 2 G x := hG.contDiffAt
  have hG' : DifferentiableAt ℝ (fderiv ℝ G) x :=
    (hGx.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsymm2 : IsSymmSndFDerivAt ℝ G x :=
    hGx.isSymmSndFDerivAt (by norm_num)
  have hfirst : ∀ y z v w : E3,
      inner ℝ ((fderiv ℝ G y z) v) w = inner ℝ v ((fderiv ℝ G y z) w) := by
    intro y z v w
    have hGy : DifferentiableAt ℝ G y :=
      (hG.contDiffAt.differentiableAt (by norm_num))
    have hGv : DifferentiableAt ℝ (fun t : E3 => G t v) y :=
      hGy.clm_apply (differentiableAt_const (c := v) (x := y))
    have hGw : DifferentiableAt ℝ (fun t : E3 => G t w) y :=
      hGy.clm_apply (differentiableAt_const (c := w) (x := y))
    have hGv' : fderiv ℝ (fun t : E3 => G t v) y z = (fderiv ℝ G y z) v := by
      have h := fderiv_clm_apply hGy (differentiableAt_const (c := v) (x := y))
      simpa using congrArg (fun L => L z) h
    have hGw' : fderiv ℝ (fun t : E3 => G t w) y z = (fderiv ℝ G y z) w := by
      have h := fderiv_clm_apply hGy (differentiableAt_const (c := w) (x := y))
      simpa using congrArg (fun L => L z) h
    have hleft := fderiv_inner_apply ℝ hGv (differentiableAt_const (c := w) (x := y)) z
    have hright := fderiv_inner_apply ℝ (differentiableAt_const (c := v) (x := y)) hGw z
    have hEq : (fun t : E3 => inner ℝ (G t v) w) =
        (fun t : E3 => inner ℝ v (G t w)) := by
      funext t
      exact hsym t v w
    have hder := congrArg (fun f : E3 → ℝ => fderiv ℝ f y z) hEq
    calc
      inner ℝ ((fderiv ℝ G y z) v) w = fderiv ℝ (fun t : E3 => inner ℝ (G t v) w) y z := by
        simpa [hGv'] using hleft.symm
      _ = fderiv ℝ (fun t : E3 => inner ℝ v (G t w)) y z := hder
      _ = inner ℝ v ((fderiv ℝ G y z) w) := by
        simpa [hGw'] using hright
  have heval (u z : E3) :
      fderiv ℝ (fun y : E3 => (fderiv ℝ G y) u) x z =
        (fderiv ℝ (fderiv ℝ G) x) z u := by
    have h := fderiv_clm_apply hG' (differentiableAt_const (c := u) (x := x))
    simpa using congrArg (fun L => L z) h
  constructor
  · intro r s
    rw [heval (EuclideanSpace.single s 1) (EuclideanSpace.single r 1),
      heval (EuclideanSpace.single r 1) (EuclideanSpace.single s 1)]
    exact hsymm2.eq _ _
  · intro r s v w
    let es : E3 := EuclideanSpace.single s 1
    let er : E3 := EuclideanSpace.single r 1
    have hB : DifferentiableAt ℝ (fun y : E3 => (fderiv ℝ G y) es) x :=
      hG'.clm_apply (differentiableAt_const (c := es) (x := x))
    have hA : DifferentiableAt ℝ (fun y : E3 => ((fderiv ℝ G y) es) v) x :=
      hB.clm_apply (differentiableAt_const (c := v) (x := x))
    have hC : DifferentiableAt ℝ (fun y : E3 => ((fderiv ℝ G y) es) w) x :=
      hB.clm_apply (differentiableAt_const (c := w) (x := x))
    have hAv : fderiv ℝ (fun y : E3 => ((fderiv ℝ G y) es) v) x er =
        (fderiv ℝ (fun y : E3 => (fderiv ℝ G y) es) x er) v := by
      have h := fderiv_clm_apply hB (differentiableAt_const (c := v) (x := x))
      simpa using congrArg (fun L => L er) h
    have hAw : fderiv ℝ (fun y : E3 => ((fderiv ℝ G y) es) w) x er =
        (fderiv ℝ (fun y : E3 => (fderiv ℝ G y) es) x er) w := by
      have h := fderiv_clm_apply hB (differentiableAt_const (c := w) (x := x))
      simpa using congrArg (fun L => L er) h
    have hleft := fderiv_inner_apply ℝ hA (differentiableAt_const (c := w) (x := x)) er
    have hright := fderiv_inner_apply ℝ (differentiableAt_const (c := v) (x := x)) hC er
    have hEq :
        (fun y : E3 => inner ℝ (((fderiv ℝ G y) es) v) w) =
          (fun y : E3 => inner ℝ v (((fderiv ℝ G y) es) w)) := by
      funext y
      exact hfirst y es v w
    have hder := congrArg (fun f : E3 → ℝ => fderiv ℝ f x er) hEq
    have hleft' :
        fderiv ℝ (fun y : E3 => inner ℝ (((fderiv ℝ G y) es) v) w) x er =
          inner ℝ (fderiv ℝ (fun y : E3 => ((fderiv ℝ G y) es) v) x er) w := by
      simpa using hleft
    have hright' :
        fderiv ℝ (fun y : E3 => inner ℝ v (((fderiv ℝ G y) es) w)) x er =
          inner ℝ v (fderiv ℝ (fun y : E3 => ((fderiv ℝ G y) es) w) x er) := by
      simpa using hright
    change inner ℝ ((fderiv ℝ (fun y : E3 => (fderiv ℝ G y) es) x er) v) w =
      inner ℝ v ((fderiv ℝ (fun y : E3 => (fderiv ℝ G y) es) x er) w)
    rw [← hAv, ← hleft', hder, hright', hAw]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
