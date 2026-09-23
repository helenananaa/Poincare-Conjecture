import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)
def boundedDerivativeGraph (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Set ((E3 →ᵇ V) × (E3 →ᵇ (E3 →L[ℝ] V))) :=
  {z | ∀ x : E3, HasFDerivAt (fun y : E3 => z.1 y) (z.2 x) x}

/-- **Math.** bounded derivative graph closed. -/
theorem bounded_derivative_graph_closed 
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    IsClosed (boundedDerivativeGraph V) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : NormedAddCommGroup (E3 →L[ℝ] V) := inferInstance
  letI : MetricSpace (E3 →ᵇ V) := inferInstance
  letI : MetricSpace (E3 →ᵇ (E3 →L[ℝ] V)) := inferInstance
  letI : FirstCountableTopology ((E3 →ᵇ V) × (E3 →ᵇ (E3 →L[ℝ] V))) := inferInstance
  apply IsSeqClosed.isClosed
  intro seq q hz hlim
  have hfun_tendsto : Tendsto (fun n => (seq n).1) atTop (𝓝 q.1) := by
    simpa only [Function.comp_def] using (continuous_fst.tendsto q).comp hlim
  have hderiv_tendsto : Tendsto (fun n => (seq n).2) atTop (𝓝 q.2) := by
    simpa only [Function.comp_def] using (continuous_snd.tendsto q).comp hlim
  have hfun : TendstoUniformly (fun n x => (seq n).1 x) q.1 atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hfun_tendsto
  have hderiv : TendstoUniformly (fun n x => (seq n).2 x) q.2 atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hderiv_tendsto
  have hfun_at : ∀ x, Tendsto (fun n => (seq n).1 x) atTop (𝓝 (q.1 x)) := by
    intro x
    exact hfun.tendstoUniformlyOnFilter.tendsto_at le_top
  have hrel : ∀ x, HasFDerivAt (fun y => q.1 y) (q.2 x) x := by
    intro x
    exact hasFDerivAt_of_tendstoUniformly hderiv
      (fun n y => (hz n) y) hfun_at x
  change ∀ x, HasFDerivAt (fun y => q.1 y) (q.2 x) x
  exact hrel
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
