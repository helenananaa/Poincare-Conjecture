import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixMetricGradientCurveDerivative
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem six_gradient_curve_derivative
    (A : E3 → (E3 →L[ℝ] E6)) (H : E3 →L[ℝ] E3 →L[ℝ] E6)
    (x : E3) (hA : HasFDerivAt A H x) :

    ∀ a b i j : Idx, HasDerivAt
      (fun t : ℝ => symmetricSixMatrix (A (x + t • EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) i j)
      (symmetricSixMatrix (H (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) i j) 0 :=
/- SWARM_PROOF_BEGIN -/
by
  intro a b i j
  let ea : E3 := EuclideanSpace.single a 1
  let eb : E3 := EuclideanSpace.single b 1
  let line : ℝ → E3 := fun t => x + t • ea
  have hline : HasDerivAt line ea 0 := by
    simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const ea).const_add x
  have hA' : HasFDerivAt A H (line 0) := by
    simpa [line] using hA
  have hAline : HasDerivAt (fun t : ℝ => A (line t)) (H ea) 0 := by
    simpa [Function.comp_def, line] using hA'.comp_hasDerivAt 0 hline
  have hvec : HasDerivAt (fun t : ℝ => A (line t) eb) (H ea eb) 0 := by
    have hconst : HasDerivAt (fun _ : ℝ => eb) (0 : E3) 0 :=
      hasDerivAt_const (c := eb) (x := 0)
    simpa [line, ContinuousLinearMap.flip_apply] using
      HasDerivAt.clm_apply (𝕜 := ℝ) hAline hconst
  have hcoord (k : Fin 6) :
      HasDerivAt (fun t : ℝ => (A (line t) eb) k) ((H ea eb) k) 0 := by
    let coordL : E6 →ₗ[ℝ] ℝ :=
      { toFun := fun q => q k
        map_add' := by intro q r; rfl
        map_smul' := by intro c q; rfl }
    let coord : E6 →L[ℝ] ℝ :=
      coordL.mkContinuous 1 (by
        intro q
        simpa [coordL, Real.norm_eq_abs] using
          (PiLp.norm_apply_le (p := 2) (x := q) k))
    simpa [line, Function.comp_def, coord, coordL] using
      coord.hasFDerivAt.comp_hasDerivAt 0 hvec
  fin_cases i <;> fin_cases j <;>
    simpa [symmetricSixMatrix, line, ea, eb] using hcoord _
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixMetricGradientCurveDerivative
