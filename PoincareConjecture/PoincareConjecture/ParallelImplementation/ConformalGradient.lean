import PoincareConjecture.ParallelImplementation.ConformalConnection
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.ConformalGradient
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
theorem gradientField_conformalMetric (g : RiemannianMetric I M)
    (u f : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    MorganTianLib.gradientField (conformalMetric g u hu) f hf p =
      Real.exp (-2 * u p) • MorganTianLib.gradientField g f hf p :=
/- SWARM_PROOF_BEGIN -/
by
  let G := MorganTianLib.gradientField (conformalMetric g u hu) f hf
  let F := MorganTianLib.gradientField g f hf
  let X : SmoothVectorField I M :=
    SmoothVectorField.smul (conformalFactor u) (conformalFactor_contMDiff hu) G - F
  have hX : X p = conformalFactor u p • G p - F p := by
    simp [X, SmoothVectorField.smul_apply]
  have hnew := MorganTianLib.metricInner_gradientField_eq_dir
    (conformalMetric g u hu) hf X p
  have hold := MorganTianLib.metricInner_gradientField_eq_dir g hf X p
  have hpairing :
      conformalFactor u p * g.metricInner p (G p) (X p) =
        g.metricInner p (F p) (X p) := by
    calc
      _ = (conformalMetric g u hu).metricInner p (G p) (X p) := by
        rw [conformalMetric_metricInner]
      _ = X.dir f p := by simpa [G] using hnew
      _ = g.metricInner p (F p) (X p) := by simpa [F] using hold.symm
  have hpairing' := hpairing
  rw [hX] at hpairing'
  have hself : g.metricInner p (X p) (X p) = 0 := by
    rw [hX]
    simp only [g.metricInner_sub_left, g.metricInner_smul_left]
    linarith [hpairing']
  have hzero : X p = 0 := by
    by_contra hne
    have hpos := g.metricInner_self_pos p (X p) hne
    rw [hself] at hpos
    linarith
  have hscale : conformalFactor u p • G p = F p := by
    have h := hX
    rw [hzero] at h
    exact sub_eq_zero.mp h.symm
  have hexp : Real.exp (-2 * u p) * conformalFactor u p = 1 := by
    rw [conformalFactor, ← Real.exp_add]
    ring_nf
    simp
  calc
    G p = (1 : ℝ) • G p := by simp
    _ = (Real.exp (-2 * u p) * conformalFactor u p) • G p := by rw [hexp]
    _ = Real.exp (-2 * u p) • (conformalFactor u p • G p) := by
      rw [← smul_smul]
    _ = Real.exp (-2 * u p) • F p := by rw [hscale]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalGradient
