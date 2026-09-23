import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BoundedLinearPullback
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LinearPullbackLaplacian
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearLocalClassicalIVP
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** constant diffusion local classical ivp. -/
theorem constant_diffusion_local_classical_ivp (B : E3 ≃L[ℝ] E3) (f : E3 →ᵇ ℝ) (hf : UniformContinuous f) :
    ∃ T : ℝ, 0<T ∧ ∃ u : (ℝ × E3) →ᵇ ℝ,
      (∀ x : E3, u (0,x)=f x) ∧ TendstoUniformly (fun t x => u (t,x)) f (𝓝[>] (0:ℝ)) ∧
      ∀ t ∈ Ioo (0:ℝ) T, ContDiff ℝ 2 (fun x : E3 => u (t,x)) ∧ ∀ x : E3,
        HasDerivAt (fun s : ℝ => u (s,x))
          (∑ i : Fin 3, ∑ j : Fin 3,
            (∑ k : Fin 3, B (EuclideanSpace.single k 1) i * B (EuclideanSpace.single k 1) j) *
            fderiv ℝ (fun z : E3 => fderiv ℝ (fun w : E3 => u (t,w)) z
              (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let b : C(E3, E3) := ⟨B, B.continuous⟩
  let g : E3 →ᵇ ℝ := BoundedContinuousFunction.compContinuous f b
  have hg : UniformContinuous (fun y : E3 => g y) := by
    have hfg : UniformContinuous (fun y : E3 => f (B y)) := by
      apply Metric.uniformContinuous_iff.mpr
      intro ε hε
      rcases Metric.uniformContinuous_iff.mp hf ε hε with ⟨δ, hδ, hδf⟩
      let L := B.toContinuousLinearMap
      refine ⟨δ / (‖L‖ + 1), by positivity, ?_⟩
      intro x y hxy
      apply hδf
      calc
        dist (B x) (B y) = ‖L (x - y)‖ := by
          rw [dist_eq_norm]
          change ‖L x - L y‖ = ‖L (x - y)‖
          rw [← map_sub]
        _ ≤ ‖L‖ * ‖x - y‖ := L.le_opNorm (x - y)
        _ < δ := by
          rw [dist_eq_norm] at hxy
          have hm := (lt_div_iff₀ (by positivity : 0 < ‖L‖ + 1)).mp hxy
          have hn := norm_nonneg (x - y)
          have hB := norm_nonneg L
          nlinarith
    simpa [g, b, BoundedContinuousFunction.compContinuous_apply] using hfg
  obtain ⟨T, hT, v, hv0, htrace, hv⟩ :=
    MorganTianLib.ParabolicPDE.semilinear_local_classical_ivp
      g hg (fun _ : ℝ => 0) 0 (by norm_num) (by intro a b; simp)
  let Ψ : ContinuousMap (ℝ × E3) (ℝ × E3) :=
    ⟨fun p => (p.1, B.symm p.2),
      continuous_fst.prodMk (B.symm.continuous.comp continuous_snd)⟩
  let u : (ℝ × E3) →ᵇ ℝ := BoundedContinuousFunction.compContinuous v Ψ
  have hu (t : ℝ) (x : E3) : u (t, x) = v (t, B.symm x) := by
    simp [u, Ψ, BoundedContinuousFunction.compContinuous_apply]
  refine ⟨T, hT, u, ?_, ?_, ?_⟩
  · intro x
    rw [hu]
    simpa [g, b, BoundedContinuousFunction.compContinuous_apply] using hv0 (B.symm x)
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hε' := (Metric.tendstoUniformly_iff.mp htrace) ε hε
    filter_upwards [hε'] with t ht
    intro x
    simpa [hu, g, b, BoundedContinuousFunction.compContinuous_apply] using ht (B.symm x)
  · intro t ht
    obtain ⟨hvt, hvtEq⟩ := hv t ht
    have huC : ContDiff ℝ 2 (fun z : E3 => u (t, z)) := by
      have hh : ContDiff ℝ 2 (fun z : E3 => v (t, B.symm z)) := by
        convert hvt.comp B.symm.toContinuousLinearMap.contDiff using 1
        funext z
        rfl
      have heq : (fun z : E3 => u (t, z)) = fun z => v (t, B.symm z) :=
        funext (hu t)
      rw [heq]
      exact hh
    refine ⟨huC, ?_⟩
    intro x
    have hLap :
        (∑ k : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ
          (fun w : E3 => v (t, w)) z (EuclideanSpace.single k 1))
          (B.symm x) (EuclideanSpace.single k 1)) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ k : Fin 3, B (EuclideanSpace.single k 1) i *
            B (EuclideanSpace.single k 1) j) *
          fderiv ℝ (fun z : E3 => fderiv ℝ
            (fun w : E3 => u (t, w)) z (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1) := by
      let q : E3 → ℝ := fun z => u (t, z)
      have hqAt : ContDiffAt ℝ 2 q (B.toContinuousLinearMap (B.symm x)) := by
        simpa [q] using huC.contDiffAt
      have hpull := linear_pullback_laplacian q B.toContinuousLinearMap
        (B.symm x) hqAt
      simpa [q, u, Ψ, BoundedContinuousFunction.compContinuous_apply] using hpull
    have htime : HasDerivAt (fun s : ℝ => u (s, x))
        (∑ k : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ
          (fun w : E3 => v (t, w)) z (EuclideanSpace.single k 1))
          (B.symm x) (EuclideanSpace.single k 1)) t := by
      simpa [hu] using hvtEq (B.symm x)
    rw [← hLap]
    exact htime
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
