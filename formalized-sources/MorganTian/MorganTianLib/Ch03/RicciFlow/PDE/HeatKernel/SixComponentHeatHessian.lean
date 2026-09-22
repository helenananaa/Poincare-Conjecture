import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.ParabolicPDE
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "V6" => EuclideanSpace ℝ (Fin 6)
/-- Actual finite-component heat regularity for six tensor coefficients at once. -/
theorem six_component_heat_hessian (F : E3 →ᵇ V6) (t : ℝ) (ht : 0<t) :
    let u : E3 → V6 := fun x => ∫ y : E3, euclideanHeatKernel 3 t (x-y) • F y
    ContDiff ℝ 2 u ∧ ∀ (x : E3) (i j : Fin 3),
      fderiv ℝ (fun z : E3 => fderiv ℝ u z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) =
        ∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) • F (x-y) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp
  let u : E3 → V6 := fun x => ∫ y : E3,
    euclideanHeatKernel 3 t (x-y) • F y
  change ContDiff ℝ 2 u ∧ ∀ (x : E3) (i j : Fin 3),
    fderiv ℝ (fun z : E3 => fderiv ℝ u z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) =
      ∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) • F (x-y)
  let P : Fin 6 → V6 →L[ℝ] ℝ := fun k =>
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 6 => ℝ) k
  let f : Fin 6 → E3 →ᵇ ℝ := fun k =>
    { toContinuousMap :=
        { toFun := fun x => P k (F x)
          continuous_toFun := (P k).continuous.comp F.continuous }
      map_bounded' := by
        obtain ⟨C, hC⟩ := F.bounded
        refine ⟨‖P k‖ * C, ?_⟩
        intro x y
        calc
          dist (P k (F x)) (P k (F y)) = ‖P k (F x - F y)‖ := by
            rw [dist_eq_norm, map_sub]
          _ ≤ ‖P k‖ * ‖F x - F y‖ := (P k).le_opNorm _
          _ = ‖P k‖ * dist (F x) (F y) := by rw [dist_eq_norm]
          _ ≤ ‖P k‖ * C :=
            mul_le_mul_of_nonneg_left (hC x y) (norm_nonneg _) }
  let us : Fin 6 → E3 → ℝ := fun k x =>
    ∫ y : E3, euclideanHeatKernel 3 t (x-y) * f k y
  obtain ⟨C, hC, hH⟩ := euclideanHeatKernel_three_hessian_L1
  have hKint (x : E3) :
      Integrable (fun y : E3 => euclideanHeatKernel 3 t (x-y)) volume := by
    have hmap :=
      (Measure.measurePreserving_sub_left (volume : Measure E3) x).integrable_comp_of_integrable
        ((euclideanHeatKernel_mass_semigroup 3).1 t ht |>.1)
    simpa [Function.comp_def] using hmap
  have hVint (x : E3) :
      Integrable (fun y : E3 => euclideanHeatKernel 3 t (x-y) • F y) volume := by
    exact (hKint x).smul_bdd ‖F‖ F.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => F.norm_coe_le_norm y))
  have hHint (i j : Fin 3) (x : E3) :
      Integrable (fun y : E3 =>
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) • F (x-y)) volume := by
    have hmeas : AEStronglyMeasurable (fun y : E3 => F (x-y)) volume := by
      fun_prop
    exact (hH t ht i j).1 |>.smul_bdd ‖F‖ hmeas
      (Filter.Eventually.of_forall (fun y => F.norm_coe_le_norm (x-y)))
  have hscalar (k : Fin 6) : ContDiff ℝ 2 (us k) := by
    simpa [us] using
      (euclideanHeatKernel_bounded_hessian_identification (f k) ht).1
  have hscalar_hess (k : Fin 6) (x : E3) (i j : Fin 3) :
      fderiv ℝ (fun z : E3 => fderiv ℝ (us k) z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1) =
        ∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * f k (x-y) := by
    simpa [us] using
      (euclideanHeatKernel_bounded_hessian_identification (f k) ht).2 x i j
  have hcoord_u (k : Fin 6) (x : E3) : P k (u x) = us k x := by
    change P k (∫ y : E3, euclideanHeatKernel 3 t (x-y) • F y) =
      ∫ y : E3, euclideanHeatKernel 3 t (x-y) * f k y
    rw [← (P k).integral_comp_comm (hVint x)]
    apply integral_congr_ae
    filter_upwards [] with y
    simp [f, P, smul_eq_mul]
  have hu : ContDiff ℝ 2 u := by
    apply (contDiff_piLp 2).2
    intro k
    rw [show (fun x : E3 => u x k) = us k by
      funext x
      simpa [P, PiLp.proj_apply] using hcoord_u k x]
    exact hscalar k
  have hu_diff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hfirst (k : Fin 6) (x : E3) :
      fderiv ℝ (fun z : E3 => P k (u z)) x =
        (P k).comp (fderiv ℝ u x) := by
    simpa [Function.comp_def] using
      ((P k).hasFDerivAt.comp x (hu_diff x).hasFDerivAt).fderiv
  have hgi (i : Fin 3) : ContDiff ℝ 1
      (fun z : E3 => fderiv ℝ u z (EuclideanSpace.single i 1)) := by
    have hfu : ContDiff ℝ 1 (fderiv ℝ u) :=
      hu.fderiv_right (m := 1) (by norm_num)
    simpa using
      hfu.clm_apply (contDiff_const :
        ContDiff ℝ 1 (fun _ : E3 => (EuclideanSpace.single i 1 : E3)))
  have hfirst_apply (k : Fin 6) (i : Fin 3) (x : E3) :
      P k (fderiv ℝ u x (EuclideanSpace.single i 1)) =
        fderiv ℝ (fun z : E3 => P k (u z)) x (EuclideanSpace.single i 1) := by
    have h := congrArg (fun L : E3 →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      (hfirst k x)
    simpa [ContinuousLinearMap.comp_apply] using h.symm
  have hfirst_fun (k : Fin 6) (i : Fin 3) :
      (fun z : E3 => P k (fderiv ℝ u z (EuclideanSpace.single i 1))) =
        (fun z : E3 => fderiv ℝ (us k) z (EuclideanSpace.single i 1)) := by
    funext z
    have hfun : (fun w : E3 => P k (u w)) = us k := by
      funext w
      exact hcoord_u k w
    have h := hfirst_apply k i z
    rw [hfun] at h
    exact h
  have hsecond (k : Fin 6) (i j : Fin 3) (x : E3) :
      P k (fderiv ℝ (fun z : E3 => fderiv ℝ u z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1)) =
        fderiv ℝ (fun z : E3 => P k (fderiv ℝ u z (EuclideanSpace.single i 1))) x
          (EuclideanSpace.single j 1) := by
    have h :=
      ((P k).hasFDerivAt.comp x
        ((hgi i).contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    have h' := congrArg (fun L : E3 →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) h
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using h'.symm
  refine ⟨hu, ?_⟩
  intro x i j
  ext k
  calc
    P k (fderiv ℝ (fun z : E3 => fderiv ℝ u z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1)) =
        fderiv ℝ (fun z : E3 => P k (fderiv ℝ u z (EuclideanSpace.single i 1))) x
          (EuclideanSpace.single j 1) := hsecond k i j x
    _ = fderiv ℝ (fun z : E3 => fderiv ℝ (us k) z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1) := by rw [hfirst_fun k i]
    _ = ∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * f k (x-y) :=
        hscalar_hess k x i j
    _ = ∫ y : E3, P k (fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) • F (x-y)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp [f, P, smul_eq_mul]
    _ = P k (∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) • F (x-y)) :=
        (P k).integral_comp_comm (hHint i j x)
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
