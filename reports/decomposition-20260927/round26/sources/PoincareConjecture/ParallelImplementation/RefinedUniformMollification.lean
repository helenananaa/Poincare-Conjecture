import PoincareConjecture.ProofContract.Refinement20260927.EuclideanMollifierReuse
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedUniformMollification
open PoincareConjecture.ProofContract.Refinement20260927
theorem uniform_mollification : UniformMollificationStatement :=
/- SWARM_PROOF_BEGIN -/
by
  intro F _ _ _ f K hf hK eps heps
  have hUC : UniformContinuousOn f (Metric.cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨delta, hdelta, hfdelta⟩ :=
    Metric.uniformContinuousOn_iff.mp hUC (eps / 2) (half_pos heps)
  let rho := min 1 delta
  have hrho : 0 < rho := lt_min one_pos hdelta
  refine ⟨rho, hrho, ?_⟩
  intro phi hphi x hx
  have hphi1 : phi.rOut < 1 := by
    exact (lt_min_iff.mp (show phi.rOut < min 1 delta from hphi)).1
  have hphidelta : phi.rOut < delta := by
    exact (lt_min_iff.mp (show phi.rOut < min 1 delta from hphi)).2
  have hnear : ∀ y ∈ Metric.ball x phi.rOut, dist (f y) (f x) ≤ eps / 2 := by
    intro y hy
    rw [Metric.mem_ball] at hy
    have hyK : y ∈ Metric.cthickening 1 K :=
      Metric.mem_cthickening_of_dist_le y x 1 K hx (hy.le.trans hphi1.le)
    have hxK : x ∈ Metric.cthickening 1 K :=
      Metric.self_subset_cthickening (δ := 1) K hx
    exact (hfdelta y hyK x hxK (hy.trans hphidelta)).le
  have hconv : dist (euclideanMollify phi f x) (f x) ≤ eps / 2 := by
    exact ContDiffBump.dist_normed_convolution_le
      (φ := phi) (μ := (MeasureTheory.volume : MeasureTheory.Measure CylinderAmbient))
      (x₀ := x) (ε := eps / 2)
      hf.aestronglyMeasurable hnear
  exact hconv.trans_lt (by linarith)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedUniformMollification
