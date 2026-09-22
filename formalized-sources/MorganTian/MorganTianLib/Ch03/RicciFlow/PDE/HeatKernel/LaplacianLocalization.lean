import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideDuhamelHessianThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The exact second-order localization identity, without an assumed product derivative. -/
theorem laplacian_cutoff_product_rule (chi u : E3 → ℝ)
    (hchi : ContDiff ℝ 2 chi) (hu : ContDiff ℝ 2 u) (x : E3) :
    (∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ (fun w => chi w*u w) z
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) =
    chi x*(∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ u z
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) +
    u x*(∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ chi z
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) +
    2*(∑ i : Fin 3, fderiv ℝ chi x (EuclideanSpace.single i 1)*
      fderiv ℝ u x (EuclideanSpace.single i 1)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hdiag : ∀ i : Fin 3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (fun w => chi w * u w) z
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) =
        chi x * fderiv ℝ (fun z : E3 => fderiv ℝ u z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) +
        u x * fderiv ℝ (fun z : E3 => fderiv ℝ chi z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) +
        2 * (fderiv ℝ chi x (EuclideanSpace.single i 1) *
          fderiv ℝ u x (EuclideanSpace.single i 1)) := by
    intro i
    let d : E3 := EuclideanSpace.single i 1
    have hχx : HasFDerivAt chi (fderiv ℝ chi x) x := by
      exact (hchi.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
    have hux : HasFDerivAt u (fderiv ℝ u x) x := by
      exact (hu.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
    have hχd : DifferentiableAt ℝ (fun z : E3 => fderiv ℝ chi z d) x := by
      have h : ContDiff ℝ 1 (fun z : E3 => fderiv ℝ chi z d) :=
        (hchi.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
      exact h.contDiffAt.differentiableAt (by norm_num)
    have hud : DifferentiableAt ℝ (fun z : E3 => fderiv ℝ u z d) x := by
      have h : ContDiff ℝ 1 (fun z : E3 => fderiv ℝ u z d) :=
        (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
      exact h.contDiffAt.differentiableAt (by norm_num)
    have hprod : ∀ z : E3,
        fderiv ℝ (fun w : E3 => chi w * u w) z d =
          chi z * fderiv ℝ u z d + u z * fderiv ℝ chi z d := by
      intro z
      have hχz : DifferentiableAt ℝ chi z :=
        hchi.contDiffAt.differentiableAt (by norm_num)
      have huz : DifferentiableAt ℝ u z :=
        hu.contDiffAt.differentiableAt (by norm_num)
      have h := fderiv_fun_mul hχz huz
      have h' := congrArg (fun L : E3 →L[ℝ] ℝ => L d) h
      simpa [smul_eq_mul] using h'
    have hsum :=
      (hχx.mul hud.hasFDerivAt).add (hux.mul hχd.hasFDerivAt)
    have hi :
        fderiv ℝ (fun z : E3 => fderiv ℝ (fun w => chi w * u w) z d) x d =
          chi x * fderiv ℝ (fun z : E3 => fderiv ℝ u z d) x d +
          u x * fderiv ℝ (fun z : E3 => fderiv ℝ chi z d) x d +
          2 * (fderiv ℝ chi x d * fderiv ℝ u x d) := by
      rw [Filter.EventuallyEq.fderiv_eq (Filter.Eventually.of_forall hprod),
        show (fun z : E3 => chi z * fderiv ℝ u z d + u z * fderiv ℝ chi z d) =
          (chi * (fun z : E3 => fderiv ℝ u z d) +
            u * (fun z : E3 => fderiv ℝ chi z d)) from rfl, hsum.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      ring
    simpa [d] using hi
  calc
    (∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ (fun w => chi w * u w) z
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) =
        ∑ i : Fin 3, (chi x * fderiv ℝ (fun z : E3 => fderiv ℝ u z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) +
          u x * fderiv ℝ (fun z : E3 => fderiv ℝ chi z
            (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) +
          2 * (fderiv ℝ chi x (EuclideanSpace.single i 1) *
            fderiv ℝ u x (EuclideanSpace.single i 1))) := by
          exact Finset.sum_congr rfl (fun i _ => hdiag i)
    _ = chi x * (∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ u z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) +
        u x * (∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ chi z
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) +
        2 * (∑ i : Fin 3, fderiv ℝ chi x (EuclideanSpace.single i 1) *
          fderiv ℝ u x (EuclideanSpace.single i 1)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
