import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveClassicalSolution
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalInitialTrace
import Mathlib.Topology.UniformSpace.HeineCantor
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** An actual three-dimensional heat initial-value solution with smooth compact initial datum. -/
theorem exists_three_dimensional_classical_heat_solution_recursive
    (f : E3 → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ u : ℝ → E3 → ℝ, u 0 = f ∧
      (∀ t : ℝ, 0 < t → ∀ x : E3,
        u t x = ∫ y : E3, euclideanHeatKernel 3 t (x - y) * f y) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E3 => u p.1 p.2) (Ioi (0 : ℝ) ×ˢ (univ : Set E3)) ∧
      TendstoUniformly u f (𝓝[>] (0 : ℝ)) ∧
      ∀ t : ℝ, 0 < t → ∀ x : E3,
        HasDerivAt (fun s => u s x) (∑ i : Fin 3, iteratedDeriv 2
          (fun z : ℝ => u t (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i z))) (x i)) t := by
/- SWARM_PROOF_BEGIN -/
  let v : ℝ → E3 → ℝ := fun t x =>
    ∫ y : E3, euclideanHeatKernel 3 t (x - y) * f y
  obtain ⟨hint, hsmooth, hderiv⟩ :=
    euclideanHeatKernel_three_compact_classical_recursive f hf hfc
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hfc
  let F : E3 →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨f, hf.continuous⟩ (2 * C) (by
      intro x y
      calc
        dist (f x) (f y) = ‖f x - f y‖ := Real.dist_eq _ _
        _ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hC x) (hC y)
        _ = 2 * C := by ring)
  have hFuc : UniformContinuous F := hfc.uniformContinuous_of_continuous hf.continuous
  let u : ℝ → E3 → ℝ := fun t x => if 0 < t then v t x else f x
  have hchange (t : ℝ) (ht : 0 < t) (x : E3) :
      (∫ y : E3, euclideanHeatKernel 3 t (x - y) * f y) =
        ∫ y : E3, euclideanHeatKernel 3 t y * F (x - y) := by
    have hmap := (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
      (MeasurableEquiv.subLeft x).measurableEmbedding
      (fun z : E3 => euclideanHeatKernel 3 t z * f (x - z))
    simpa [F, sub_sub_cancel] using hmap
  have htrace := euclideanHeatKernel_three_uniform_initial_trace F hFuc
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    simp [u]
  · intro t ht x
    simp [u, v, ht]
  · apply hsmooth.congr
    intro p hp
    have hp' : 0 < p.1 := hp.1
    simp [u, v, hp']
  · apply (tendstoUniformly_congr ?_).mp htrace
    filter_upwards [self_mem_nhdsWithin] with t ht
    funext x
    have ht' : 0 < t := ht
    rw [show u t x = v t x by
      dsimp [u]
      rw [if_pos ht']]
    exact (hchange t ht x).symm
  · intro t ht x
    have hv : HasDerivAt (fun s => v s x)
        (∑ i : Fin 3, iteratedDeriv 2
          (fun z : ℝ => v t (WithLp.toLp 2
            (Function.update (WithLp.ofLp x) i z))) (x i)) t := by
      simpa [v] using hderiv t ht x
    have hev : (fun s => u s x) =ᶠ[𝓝 t] (fun s => v s x) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      have hs' : 0 < s := hs
      dsimp [u]
      rw [if_pos hs']
    have hu := hv.congr_of_eventuallyEq hev
    have hcoeff :
        (∑ i : Fin 3, iteratedDeriv 2
            (fun z : ℝ => v t (WithLp.toLp 2
              (Function.update (WithLp.ofLp x) i z))) (x i)) =
          ∑ i : Fin 3, iteratedDeriv 2
            (fun z : ℝ => u t (WithLp.toLp 2
              (Function.update (WithLp.ofLp x) i z))) (x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      funext z
      simp [u, ht]
    rw [hcoeff] at hu
    exact hu
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
