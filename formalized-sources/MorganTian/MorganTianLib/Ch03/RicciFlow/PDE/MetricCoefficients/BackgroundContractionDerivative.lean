import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BackgroundConnectionContraction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** background contraction derivative. -/
theorem background_contraction_derivative (G : E3 → (E3 →L[ℝ] E3)) (T : E3 → T3) (x v : E3)
    (hG : DifferentiableAt ℝ G x) (hT : DifferentiableAt ℝ T x)
    (c : ℝ) (hc : 0<c) (hpos : ∀ w : E3, c*‖w‖^2 ≤ inner ℝ (G x w) w) (k : Fin 3) :
    (fderiv ℝ (fun y => backgroundConnectionContraction (G y) (T y)) x v) k =
      ∑ i : Fin 3, ∑ j : Fin 3, (
        ((-((G x).inverse.comp ((fderiv ℝ G x v).comp (G x).inverse)))
          (EuclideanSpace.single j 1)) i * T x k i j +
        ((G x).inverse (EuclideanSpace.single j 1)) i *
          fderiv ℝ (fun y => T y k i j) x v) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let dInv (i j : Fin 3) : E3 →L[ℝ] ℝ :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp
      (((fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) (G x)).comp
        (fderiv ℝ G x)).flip (EuclideanSpace.single j (1 : ℝ)))
  let dT (i j : Fin 3) : E3 →L[ℝ] ℝ :=
    fderiv ℝ (fun y : E3 => T y k i j) x
  let dTerm (i j : Fin 3) : E3 →L[ℝ] ℝ :=
    ((G x).inverse (EuclideanSpace.single j (1 : ℝ)) i) • dT i j +
      (T x k i j) • dInv i j
  let f : E3 → ℝ := fun y => ∑ i : Fin 3, ∑ j : Fin 3,
    ((G y).inverse (EuclideanSpace.single j (1 : ℝ)) i) * T y k i j

  have hInvCD : ContDiffAt ℝ ∞ (fun B : E3 →L[ℝ] E3 => B.inverse) (G x) :=
    (coercive_inverse_differential (G x) c hc hpos).1
  have hInvField : HasFDerivAt (fun y : E3 => (G y).inverse)
      ((fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) (G x)).comp
        (fderiv ℝ G x)) x := by
    exact (hInvCD.differentiableAt (by norm_num)).hasFDerivAt.comp x hG.hasFDerivAt

  have hInvCoord : ∀ i j : Fin 3,
      HasFDerivAt (fun y : E3 => ((G y).inverse (EuclideanSpace.single j (1 : ℝ))) i)
        (dInv i j) x := by
    intro i j
    have happly := hInvField.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) x)
    have happly' : HasFDerivAt
        (fun y : E3 => (G y).inverse (EuclideanSpace.single j (1 : ℝ)))
        (((fderiv ℝ (fun B : E3 →L[ℝ] E3 => B.inverse) (G x)).comp
          (fderiv ℝ G x)).flip (EuclideanSpace.single j (1 : ℝ))) x := by
      simpa using happly
    simpa [dInv, Function.comp_def, EuclideanSpace.coe_proj] using
      ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x happly')

  have hTCoordDiff : ∀ i j : Fin 3,
      DifferentiableAt ℝ (fun y : E3 => T y k i j) x := by
    intro i j
    have h1 : DifferentiableAt ℝ (fun y : E3 => T y k) x := by
      exact (ContinuousLinearMap.proj (R := ℝ) k).differentiableAt.comp x hT
    have h2 : DifferentiableAt ℝ (fun y : E3 => T y k i) x := by
      exact (ContinuousLinearMap.proj (R := ℝ) i).differentiableAt.comp x h1
    exact (ContinuousLinearMap.proj (R := ℝ) j).differentiableAt.comp x h2

  have hterm : ∀ i j : Fin 3,
      HasFDerivAt
        (fun y : E3 => ((G y).inverse (EuclideanSpace.single j (1 : ℝ)) i) * T y k i j)
        (dTerm i j) x := by
    intro i j
    have ht : HasFDerivAt (fun y : E3 => T y k i j) (dT i j) x := by
      simpa [dT] using (hTCoordDiff i j).hasFDerivAt
    convert (hInvCoord i j).mul ht using 1
    all_goals try apply Subsingleton.elim
    all_goals try rfl
    all_goals ext y <;> simp [dTerm]

  have hsumj : ∀ i : Fin 3,
      HasFDerivAt (fun y : E3 => ∑ j : Fin 3,
          ((G y).inverse (EuclideanSpace.single j (1 : ℝ)) i) * T y k i j)
      (∑ j : Fin 3, dTerm i j) x := by
    intro i
    convert HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
      (fun j _ => hterm i j) using 1
    all_goals try apply Subsingleton.elim
    all_goals try rfl
    all_goals ext y <;> simp
  have hF : HasFDerivAt f (∑ i : Fin 3, ∑ j : Fin 3, dTerm i j) x := by
    convert HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
      (fun i _ => hsumj i) using 1
    all_goals try apply Subsingleton.elim
    all_goals try rfl
    all_goals ext y <;> simp [f]

  have hOutDiff : DifferentiableAt ℝ
      (fun y : E3 => backgroundConnectionContraction (G y) (T y)) x := by
    have hB := background_connection_contraction_smooth (G x) (T x) c hc hpos
    have hPair : DifferentiableAt ℝ (fun y : E3 => (G y, T y)) x := hG.prodMk hT
    exact DifferentiableAt.comp
      (f := fun y : E3 => (G y, T y))
      (g := fun z : (E3 →L[ℝ] E3) × T3 => backgroundConnectionContraction z.1 z.2)
      x (hB.differentiableAt (by norm_num)) hPair
  have hproj : HasFDerivAt
      (fun y : E3 => backgroundConnectionContraction (G y) (T y) k)
      ((EuclideanSpace.proj (𝕜 := ℝ) k).comp
        (fderiv ℝ (fun y : E3 => backgroundConnectionContraction (G y) (T y)) x)) x := by
    simpa [Function.comp_def] using
      ((EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp x hOutDiff.hasFDerivAt)
  have hfun : (fun y : E3 => backgroundConnectionContraction (G y) (T y) k) = f := by
    funext y
    simp [f, backgroundConnectionContraction]

  have hinv := (coercive_inverse_differential (G x) c hc hpos).2
  have hInvEval : ∀ i j : Fin 3,
      dInv i j v =
        ((-((G x).inverse.comp ((fderiv ℝ G x v).comp (G x).inverse)))
          (EuclideanSpace.single j (1 : ℝ))) i := by
    intro i j
    have hformula := hinv (fderiv ℝ G x v)
    simp [dInv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, hformula]

  calc
    (fderiv ℝ (fun y : E3 => backgroundConnectionContraction (G y) (T y)) x v) k =
        ((EuclideanSpace.proj (𝕜 := ℝ) k).comp
          (fderiv ℝ (fun y : E3 => backgroundConnectionContraction (G y) (T y)) x)) v := by
            simp [ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj]
    _ = (fderiv ℝ (fun y : E3 => backgroundConnectionContraction (G y) (T y) k) x) v := by
          rw [← hproj.fderiv]
    _ = (fderiv ℝ f x) v := by rw [hfun]
    _ = (∑ i : Fin 3, ∑ j : Fin 3, dTerm i j) v := by rw [hF.fderiv]
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
          (((-((G x).inverse.comp ((fderiv ℝ G x v).comp (G x).inverse)))
              (EuclideanSpace.single j (1 : ℝ))) i * T x k i j +
            ((G x).inverse (EuclideanSpace.single j (1 : ℝ))) i *
              fderiv ℝ (fun y => T y k i j) x v) := by
          simp only [ContinuousLinearMap.sum_apply, dTerm, dT]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
          rw [hInvEval i j]
          ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
