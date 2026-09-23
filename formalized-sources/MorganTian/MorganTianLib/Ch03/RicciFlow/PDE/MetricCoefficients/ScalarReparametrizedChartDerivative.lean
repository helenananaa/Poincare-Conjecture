import MorganTianLib.Ch01.CurvatureFrameBridge
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartCoefficientOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** scalar reparametrized chart derivative. -/
theorem scalar_reparametrized_chart_derivative {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r))
    (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) (f : M → ℝ) (hf : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ f) (i : Fin 3) :
    fderiv ℝ (fun z : E3 => f ((extChartAt (𝓡 3) a).symm (B z))) x
      (EuclideanSpace.single i 1) =
    mfderiv (𝓡 3) 𝓘(ℝ) f ((extChartAt (𝓡 3) a).symm (B x))
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i)
        ((extChartAt (𝓡 3) a).symm (B x))) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let φ := extChartAt (𝓡 3) a
  let q := φ.symm (B x)
  let F : E3 → ℝ := fun y => f (φ.symm y)
  have hq : q ∈ (chartAt E3 a).source := by
    dsimp [q, φ]
    simpa [extChartAt_source] using (extChartAt (𝓡 3) a).map_target hx
  have hyt : (extChartAt (𝓡 3) a) q = B x := by
    dsimp [q]
    exact (extChartAt (𝓡 3) a).right_inv hx
  have hFmd : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F (B x) := by
    dsimp [F, φ]
    exact ContMDiffAt.comp _ hf.contMDiffAt
      ((contMDiffOn_extChartAt_symm a _ hx).contMDiffAt
        (extChartAt_target_mem_nhds' hx))
  have hFdiff : DifferentiableAt ℝ F (B x) := by
    exact mdifferentiableAt_iff_differentiableAt.mp
      (hFmd.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
  have hFdiffq : DifferentiableAt ℝ F ((extChartAt (𝓡 3) a) q) := by
    rw [hyt]
    exact hFdiff
  have hchain : fderiv ℝ (F ∘ B) x =
      (fderiv ℝ F (B x)).comp B.toContinuousLinearMap := by
    exact (hFdiff.hasFDerivAt.comp x B.toContinuousLinearMap.hasFDerivAt).fderiv
  have hfeq : f =ᶠ[𝓝 q] (fun z : M => F ((extChartAt (𝓡 3) a) z)) := by
    filter_upwards [(chartAt E3 a).open_source.mem_nhds hq] with r hr
    have hr' : r ∈ (extChartAt (𝓡 3) a).source := by
      rwa [extChartAt_source]
    change f r = F ((extChartAt (𝓡 3) a) r)
    dsimp [F]
    change f r = f ((chartAt E3 a).symm ((chartAt E3 a) r))
    rw [(chartAt E3 a).left_inv hr]
  have hcoord := mfderiv_comp_extChartAt_chartBasisVecFiber
      (I := 𝓡 3) hq hFdiffq (e i)
  calc
    fderiv ℝ (fun z : E3 => f ((extChartAt (𝓡 3) a).symm (B z))) x
        (EuclideanSpace.single i 1) =
        fderiv ℝ (F ∘ B) x (EuclideanSpace.single i 1) := rfl
    _ = fderiv ℝ F (B x) (B (EuclideanSpace.single i 1)) := by
      rw [hchain]
      rfl
    _ = fderiv ℝ F (B x) (Module.finBasis ℝ E3 (e i)) := by
      rw [hB i]
    _ = Riemannian.partialDeriv (e i) F (B x) := by
      simp [Riemannian.partialDeriv]
    _ = mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun z : M => F ((extChartAt (𝓡 3) a) z)) q
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) q) := by
      rw [← hyt]
      exact hcoord.symm
    _ = mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f q
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) q) := by
      rw [← hfeq.mfderiv_eq]
      rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
