import PoincareConjecture.ProofContract.Refinement20260927.NeckLoss
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedFiniteCapScaling
open PoincareConjecture.ProofContract.Refinement20260927
theorem finite_cap_scaling : FiniteCapScalingStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro n caps r hr
  have hdim : Module.finrank ℝ PoincareConjecture.ProofContract.V1.Euclidean3 = 3 := by
    simp [PoincareConjecture.ProofContract.V1.Euclidean3]
  have hsqrt : Real.sqrt ((r ^ 2) ^ 3) = r ^ 3 := by
    rw [show (r ^ 2) ^ 3 = (r ^ 3) ^ 2 by ring]
    exact Real.sqrt_sq (pow_nonneg hr.le 3)
  have hone (i : Fin n) :
      (caps i).scaledVolume r hr =
        ENNReal.ofReal (r ^ 3 * (caps i).baseVolume) := by
    let c := caps i
    have hfinite : regionMeasure c.metric c.region < ⊤ :=
      MorganTianLib.riemannianMeasure_lt_top_of_isCompact
        (MeasureTheory.volume : MeasureTheory.Measure
          PoincareConjecture.ProofContract.V1.Euclidean3)
        c.metric c.compact
    change c.scaledVolume r hr = _
    simp only [CompactCapModel.scaledVolume, CompactCapModel.scaledMeasure,
      CompactCapModel.baseVolume, regionMeasure]
    rw [MorganTianLib.rescaledMetric_riemannianMeasure,
      MeasureTheory.Measure.smul_apply, smul_eq_mul, hdim, hsqrt]
    have htoReal : ENNReal.ofReal ((regionMeasure c.metric c.region).toReal) =
        regionMeasure c.metric c.region := ENNReal.ofReal_toReal hfinite.ne
    calc
      ENNReal.ofReal (r ^ 3) * regionMeasure c.metric c.region =
          ENNReal.ofReal (r ^ 3) *
            ENNReal.ofReal ((regionMeasure c.metric c.region).toReal) := by
        exact congrArg (fun x : ENNReal => ENNReal.ofReal (r ^ 3) * x) htoReal.symm
      _ = ENNReal.ofReal (r ^ 3 * (regionMeasure c.metric c.region).toReal) := by
        rw [← ENNReal.ofReal_mul (pow_nonneg hr.le 3)]
  calc
    (∑ i, (caps i).scaledVolume r hr) =
        ∑ i, ENNReal.ofReal (r ^ 3 * (caps i).baseVolume) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hone i
    _ = ENNReal.ofReal (∑ i, r ^ 3 * (caps i).baseVolume) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i hi
      exact mul_nonneg (pow_nonneg hr.le 3) ENNReal.toReal_nonneg
    _ = ENNReal.ofReal (r ^ 3 * ∑ i, (caps i).baseVolume) := by
      congr 1
      rw [Finset.mul_sum]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedFiniteCapScaling
