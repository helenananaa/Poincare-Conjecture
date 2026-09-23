import PoincareConjecture.ParallelImplementation.ConformalConnection
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.ConformalMetricBasis
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
theorem exists_conformal_metric_basis (g : RiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0) :
    ∃ b' : Module.Basis ι ℝ (TangentSpace I p),
      (∀ i, b' i = Real.exp (-u p) • b i) ∧
      (∀ i j, (conformalMetric g u hu).metricInner p (b' i) (b' j) =
        if i = j then 1 else 0) :=
/- SWARM_PROOF_BEGIN -/
by
  let c : ℝˣ := Units.mk0 (Real.exp (-u p)) (Real.exp_ne_zero _)
  let b' : Module.Basis ι ℝ (TangentSpace I p) := b.unitsSMul (fun _ => c)
  have hbi (i : ι) : b' i = Real.exp (-u p) • b i := by
    simpa [b', c, Units.val_mk0] using (b.unitsSMul_apply (w := fun _ => c) i)
  refine ⟨b', ?_, ?_⟩
  · intro i
    exact hbi i
  · intro i j
    have hpair :
        (conformalMetric g u hu).metricInner p (b' i) (b' j) =
          Real.exp (2 * u p) *
            (Real.exp (-u p) * (Real.exp (-u p) * g.metricInner p (b i) (b j))) := by
      rw [conformalMetric_metricInner g hu p, hbi i, hbi j,
        g.metricInner_smul_left, g.metricInner_smul_right]
      rfl
    rw [hpair]
    by_cases hij : i = j
    · subst j
      have hdiag : g.metricInner p (b i) (b i) = 1 := by
        simpa using hb i i
      rw [hdiag]
      simp only [mul_one]
      calc
        Real.exp (2 * u p) *
            (Real.exp (-u p) * Real.exp (-u p)) =
              Real.exp (2 * u p + (-u p + -u p)) := by
                rw [← Real.exp_add, ← Real.exp_add]
        _ = 1 := by
          have hexp : 2 * u p + (-u p + -u p) = 0 := by ring
          rw [hexp, Real.exp_zero]
    · have hoff : g.metricInner p (b i) (b j) = 0 := by
        simpa [hij] using hb i j
      rw [hoff]
      simp [hij]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalMetricBasis
