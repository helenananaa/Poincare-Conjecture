import MorganTianLib.Ch02.Laplacian
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle BigOperators
namespace PoincareConjecture.ParallelImplementation.MetricTraceBasis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
theorem laplacianAt_eq_sum_of_metric_basis
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0) :
    MorganTianLib.laplacianAt g nabla f p =
      ∑ i, MorganTianLib.hessianAt nabla f p (b i) (b i) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  have horth : Orthonormal ℝ b := by
    rw [orthonormal_iff_ite]
    exact hb
  simpa only [Module.Basis.coe_toOrthonormalBasis] using
    (MorganTianLib.laplacianAt_eq_sum g nabla hf p (b.toOrthonormalBasis horth))
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.MetricTraceBasis
