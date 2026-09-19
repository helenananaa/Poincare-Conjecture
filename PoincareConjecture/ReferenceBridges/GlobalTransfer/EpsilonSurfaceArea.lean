import ReferenceBridges.GlobalTransfer.EpsilonAllPairs
import ReferenceBridges.GlobalTransfer.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory Riemannian Manifold
open scoped Topology BigOperators Manifold ContDiff ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Actual epsilon-close metrics control differential surface density and its extended integral without excluding singular points. -/
theorem epsilonClose_parametrized_area {ε : ℝ} (g0 g : RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose ε g0 g)
    (F : EuclideanSpace ℝ (Fin 2) → M) (μ : Measure (EuclideanSpace ℝ (Fin 2))) :
    (∀ x, (1-ε)*paramAreaDensity g0 F x ≤ paramAreaDensity g F x ∧
      paramAreaDensity g F x ≤ (1+ε)*paramAreaDensity g0 F x) ∧
    ENNReal.ofReal (1-ε) * (∫⁻ x, ENNReal.ofReal (paramAreaDensity g0 F x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (paramAreaDensity g F x) ∂μ ∧
    (∫⁻ x, ENNReal.ofReal (paramAreaDensity g F x) ∂μ) ≤
      ENNReal.ofReal (1+ε) * (∫⁻ x, ENNReal.ofReal (paramAreaDensity g0 F x) ∂μ) :=
/- SWARM_PROOF_BEGIN -/
by
  have he0 : 0 < ε := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.1
  have hehalf : ε < 1 / 2 := by
    rw [MorganTianLib.EpsilonClose] at h
    exact h.2.1
  have hlo : 0 ≤ 1 - ε :=
    sub_nonneg.mpr (hehalf.trans (by norm_num : (1 : ℝ) / 2 < 1)).le
  have hhi : 0 ≤ 1 + ε := add_nonneg (by norm_num) he0.le
  have hpt : ∀ x, (1 - ε) * paramAreaDensity g0 F x ≤ paramAreaDensity g F x ∧
      paramAreaDensity g F x ≤ (1 + ε) * paramAreaDensity g0 F x := by
    intro x
    unfold paramAreaDensity
    exact epsilonClose_all_pair_area g0 g h (F x)
      (mfderiv (𝓡 2) I F x (EuclideanSpace.single 0 1))
      (mfderiv (𝓡 2) I F x (EuclideanSpace.single 1 1))
  refine ⟨hpt, ?_, ?_⟩
  · calc
      ENNReal.ofReal (1 - ε) *
          (∫⁻ x, ENNReal.ofReal (paramAreaDensity g0 F x) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (1 - ε) *
          ENNReal.ofReal (paramAreaDensity g0 F x) ∂μ := by
        exact (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (paramAreaDensity g F x) ∂μ := by
        apply MeasureTheory.lintegral_mono
        intro x
        change
          ENNReal.ofReal (1 - ε) * ENNReal.ofReal (paramAreaDensity g0 F x) ≤
            ENNReal.ofReal (paramAreaDensity g F x)
        rw [← ENNReal.ofReal_mul hlo]
        exact ENNReal.ofReal_le_ofReal (hpt x).1
  · calc
      (∫⁻ x, ENNReal.ofReal (paramAreaDensity g F x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (1 + ε) *
          ENNReal.ofReal (paramAreaDensity g0 F x) ∂μ := by
        apply MeasureTheory.lintegral_mono
        intro x
        change
          ENNReal.ofReal (paramAreaDensity g F x) ≤
            ENNReal.ofReal (1 + ε) * ENNReal.ofReal (paramAreaDensity g0 F x)
        rw [← ENNReal.ofReal_mul hhi]
        exact ENNReal.ofReal_le_ofReal (hpt x).2
      _ = ENNReal.ofReal (1 + ε) *
          (∫⁻ x, ENNReal.ofReal (paramAreaDensity g0 F x) ∂μ) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
