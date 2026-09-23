import PoincareConjecture.ParallelImplementation.MetricTraceBasis
import PoincareConjecture.ParallelImplementation.ConformalPointHessian
import PoincareConjecture.ParallelImplementation.ConformalMetricBasis
import PoincareConjecture.ParallelImplementation.MetricGradientContraction
import PoincareConjecture.ParallelImplementation.ConformalHessian
import PoincareConjecture.ParallelImplementation.ConformalGradient
import MorganTianLib.Ch02.Laplacian
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle BigOperators
namespace PoincareConjecture.ParallelImplementation.ConformalLaplacianRecovered
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
theorem laplacianAt_conformalMetric (g : RiemannianMetric I M)
    (u f : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    MorganTianLib.laplacianAt (conformalMetric g u hu)
      (conformalMetric g u hu).leviCivitaConnection f p =
    Real.exp (-2 * u p) * (MorganTianLib.laplacianAt g g.leviCivitaConnection f p +
      ((Module.finrank ℝ E : ℝ) - 2) * (MorganTianLib.gradientField g u hu).dir f p) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let ob : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    stdOrthonormalBasis ℝ (TangentSpace I p)
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) := ob.toBasis
  have horth : Orthonormal ℝ (fun i => b i) := by
    simpa [b, OrthonormalBasis.coe_toBasis] using ob.orthonormal
  have hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    have h := (orthonormal_iff_ite.mp horth) i j
    change inner ℝ (b i) (b j) = if i = j then 1 else 0 at h
    change inner ℝ (b i) (b j) = if i = j then 1 else 0
    exact h
  obtain ⟨b', hb'scale, hb'⟩ :=
    PoincareConjecture.ParallelImplementation.ConformalMetricBasis.exists_conformal_metric_basis
      g u hu p b hb
  have htraceG : MorganTianLib.laplacianAt g g.leviCivitaConnection f p =
      ∑ i, MorganTianLib.hessianAt g.leviCivitaConnection f p (b i) (b i) := by
    exact PoincareConjecture.ParallelImplementation.MetricTraceBasis.laplacianAt_eq_sum_of_metric_basis
      g g.leviCivitaConnection f hf p b hb
  have htraceT : MorganTianLib.laplacianAt (conformalMetric g u hu)
      (conformalMetric g u hu).leviCivitaConnection f p =
      ∑ i, MorganTianLib.hessianAt (conformalMetric g u hu).leviCivitaConnection
        f p (b' i) (b' i) := by
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨(conformalMetric g u hu).toRiemannianMetric⟩
    exact PoincareConjecture.ParallelImplementation.MetricTraceBasis.laplacianAt_eq_sum_of_metric_basis
      (conformalMetric g u hu) (conformalMetric g u hu).leviCivitaConnection f hf p b' hb'
  have hessianScale (i : Fin (Module.finrank ℝ E)) :
      MorganTianLib.hessianAt g.leviCivitaConnection f p
          (Real.exp (-u p) • b i) (Real.exp (-u p) • b i) =
        Real.exp (-2 * u p) *
          MorganTianLib.hessianAt g.leviCivitaConnection f p (b i) (b i) := by
    rw [MorganTianLib.hessianAt_smul_left, MorganTianLib.hessianAt_smul_right _ hf]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2 <;> ring_nf
  have hpoint (i : Fin (Module.finrank ℝ E)) :
      MorganTianLib.hessianAt (conformalMetric g u hu).leviCivitaConnection f p
          (b' i) (b' i) =
        Real.exp (-2 * u p) *
          (MorganTianLib.hessianAt g.leviCivitaConnection f p (b i) (b i) -
            2 * PoincareConjecture.ParallelImplementation.ConformalPointHessian.scalarDifferential
              u p (b i) * PoincareConjecture.ParallelImplementation.ConformalPointHessian.scalarDifferential
              f p (b i) +
            (MorganTianLib.gradientField g u hu).dir f p) := by
    rw [PoincareConjecture.ParallelImplementation.ConformalPointHessian.hessianAt_conformalMetric
      g u f hu hf p (b' i) (b' i), hb'scale i, hessianScale i]
    simp only [PoincareConjecture.ParallelImplementation.ConformalPointHessian.scalarDifferential,
      map_smul, smul_eq_mul, conformalMetric_metricInner g hu]
    rw [g.metricInner_smul_left, g.metricInner_smul_right, hb i i]
    have hexp : Real.exp (-u p) * Real.exp (-u p) = Real.exp (-2 * u p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    simp
    ring_nf
  have hcontract :=
    PoincareConjecture.ParallelImplementation.MetricGradientContraction.sum_metric_basis_derivatives_eq_gradient_pairing
      g u f hu hf p b hb
  have hcontract' :
      (∑ i : Fin (Module.finrank ℝ E),
        PoincareConjecture.ParallelImplementation.ConformalPointHessian.scalarDifferential
          u p (b i) *
          PoincareConjecture.ParallelImplementation.ConformalPointHessian.scalarDifferential
            f p (b i)) =
        (MorganTianLib.gradientField g u hu).dir f p := by
    simpa [PoincareConjecture.ParallelImplementation.MetricGradientContraction.scalarDifferential,
      PoincareConjecture.ParallelImplementation.ConformalPointHessian.scalarDifferential]
      using hcontract
  have hsum :
      (∑ i : Fin (Module.finrank ℝ E),
        (MorganTianLib.hessianAt g.leviCivitaConnection f p (b i) (b i) -
          2 * PoincareConjecture.ParallelImplementation.ConformalPointHessian.scalarDifferential
            u p (b i) * PoincareConjecture.ParallelImplementation.ConformalPointHessian.scalarDifferential
            f p (b i) +
          (MorganTianLib.gradientField g u hu).dir f p)) =
      MorganTianLib.laplacianAt g g.leviCivitaConnection f p +
        ((Module.finrank ℝ E : ℝ) - 2) *
          (MorganTianLib.gradientField g u hu).dir f p := by
    rw [htraceG]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hcontract']
    simp [Finset.sum_const, Fintype.card_fin]
    ring
  rw [htraceT]
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  rw [hsum]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalLaplacianRecovered
