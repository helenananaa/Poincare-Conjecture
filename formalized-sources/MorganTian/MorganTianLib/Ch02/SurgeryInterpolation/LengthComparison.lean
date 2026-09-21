import DoCarmoLib.Riemannian.Variation.SmoothEnergy

open Set MeasureTheory Riemannian Riemannian.Variation
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryInterpolation
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N] [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- **Math.** Pointwise contraction relative to a smooth pullback controls actual curve length. -/
theorem arcLength_le_of_metric_pullback_le
    (gM : RiemannianMetric I M) (gN : RiemannianMetric J N)
    (phi : M → N) (hphi : ContMDiff I J ∞ phi)
    (hdom : ∀ p v, gM.metricInner p v v ≤
      gN.metricInner (phi p) (mfderiv I J phi p v) (mfderiv I J phi p v))
    (c : ℝ → M) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c)
    {a b : ℝ} (hab : a ≤ b) :
    DCArcLength gM c a b ≤ DCArcLength gN (phi ∘ c) a b := by
  have hiM := Riemannian.Variation.ContMDiffOn.intervalIntegrable_dcSpeed_of_isOpen
    gM hab isOpen_univ (subset_univ (Icc a b)) hc.contMDiffOn
  have hiN := Riemannian.Variation.ContMDiffOn.intervalIntegrable_dcSpeed_of_isOpen
    gN hab isOpen_univ (subset_univ (Icc a b)) (hphi.comp hc).contMDiffOn
  have hspeed : ∀ t, dcSpeed gM c t ≤ dcSpeed gN (phi ∘ c) t := by
    intro t
    unfold dcSpeed
    rw [DCVelocity_comp t ((hphi.mdifferentiable (by simp)) (c t))
      ((hc.mdifferentiable (by simp)) t)]
    exact Real.sqrt_le_sqrt (hdom (c t) (DCVelocity c t))
  exact intervalIntegral.integral_mono hab hiM hiN hspeed

end MorganTianLib.SurgeryInterpolation
