import Mathlib
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** linear pullback second derivative. -/
theorem linear_pullback_second_derivative (f : E3 → ℝ) (B : E3 →L[ℝ] E3) (x v w : E3)
    (hf : ContDiffAt ℝ 2 f (B x)) :
    fderiv ℝ (fun y : E3 => fderiv ℝ (fun z : E3 => f (B z)) y v) x w =
      fderiv ℝ (fun y : E3 => fderiv ℝ f y (B v)) (B x) (B w) :=
/- SWARM_PROOF_BEGIN -/
by
  let q : E3 → ℝ := fun y => fderiv ℝ (fun z : E3 => f (B z)) y v
  let g : E3 → ℝ := fun y => fderiv ℝ f y (B v)
  have hnear : ∀ᶠ y : E3 in 𝓝 x, ContDiffAt ℝ 2 f (B y) :=
    (B.continuous.continuousAt).eventually (hf.eventually (by norm_num))
  have hchain : ∀ᶠ y : E3 in 𝓝 x,
      fderiv ℝ (fun z : E3 => f (B z)) y = (fderiv ℝ f (B y)).comp B := by
    filter_upwards [hnear] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt.comp y B.hasFDerivAt |>.fderiv
  have hev : q =ᶠ[𝓝 x] fun y => g (B y) := by
    filter_upwards [hchain] with y hy
    dsimp [q, g]
    rw [hy]
    rfl
  have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) (B x) :=
    hf.fderiv_right (by norm_num)
  have hgCont : ContDiffAt ℝ 1 g (B x) := by
    simpa only [g] using hfderiv.clm_apply (contDiffAt_const)
  have hgDiff : DifferentiableAt ℝ g (B x) := hgCont.differentiableAt (by norm_num)
  have hbase : HasFDerivAt (fun y : E3 => g (B y))
      ((fderiv ℝ g (B x)).comp B) x := by
    simpa only [Function.comp_def] using
      (hgDiff.hasFDerivAt.comp x B.hasFDerivAt)
  have hresult := hbase.congr_of_eventuallyEq hev
  rw [hresult.fderiv]
  rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
