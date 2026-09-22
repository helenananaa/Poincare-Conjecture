import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildExistence
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearInitialTrace
open Set MeasureTheory Filter Function
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- A positive-lifespan mild initial-value problem for actual semilinear heat flow. -/
theorem semilinear_local_mild_ivp (f : E3 →ᵇ ℝ) (hf : UniformContinuous f)
    (N : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hN : ∀ a b : ℝ, |N a-N b| ≤ L*|a-b|) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : (ℝ × E3) →ᵇ ℝ,
      (∀ x, u (0,x)=f x) ∧ TendstoUniformly (fun t x => u (t,x)) f (𝓝[>] (0:ℝ)) ∧
      ∀ t : ℝ, 0 < t → t ≤ T → ∀ x : E3,
        u (t,x) = (∫ y : E3, euclideanHeatKernel 3 t y * f (x-y)) +
          ∫ s in (0:ℝ)..t, ∫ y : E3, euclideanHeatKernel 3 (t-s) y * N (u (s,x-y)) :=
/- SWARM_PROOF_BEGIN -/
by
  let T : ℝ := 1 / (2 * (L + 1))
  have hLp : 0 < L + 1 := by linarith
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hTL : T * L < 1 := by
    dsimp [T]
    have h : L / (2 * (L + 1)) < 1 := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (L + 1))).2
      nlinarith
    convert h using 1 <;> ring
  obtain ⟨u, hu, -⟩ := semilinear_mild_exists_unique f hf N L T hL hT.le hTL hN
  have htrace := semilinear_mild_initial_trace f hf N L T hL hT hN u hu
  refine ⟨T, hT, u, htrace.1, htrace.2, ?_⟩
  intro t ht htT x
  have hclip : max 0 (min T t) = t := by
    rw [max_eq_right (lt_min hT ht).le, min_eq_right htT]
  rw [hu (t, x), hclip]
  simp [ht.ne']
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
