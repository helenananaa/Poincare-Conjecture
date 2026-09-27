import PoincareConjecture.ProofContract.Refinement20260927.NeckLoss
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedUniformNeckAllowance
open PoincareConjecture.ProofContract.Refinement20260927
theorem uniform_neck_allowance : UniformNeckAllowanceStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := ⟨by simp⟩
  intro B hB
  let sphere0 : {p : EuclideanSpace ℝ (Fin (2 + 1)) //
      p ∈ MorganTianLib.EpsilonNeckSphere} :=
    ⟨EuclideanSpace.single 0 1, by simp [MorganTianLib.EpsilonNeckSphere]⟩
  obtain ⟨a0, ha0, hround⟩ :=
    MorganTianLib.roundCylinder_fractional_region_volume_lower
      (MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin (2 + 1)))) sphere0
  let epsilon0 : ℝ := min (1 / 2) (a0 / (4 * (B + 1)))
  have hepsilon0 : 0 < epsilon0 := by
    dsimp [epsilon0]
    apply lt_min
    · norm_num
    · apply div_pos ha0
      positivity
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro M g x epsilon hepsilon hepsilonSmall S
  have hepsilonHalf : epsilon < 1 / 2 :=
    lt_of_lt_of_le hepsilonSmall (min_le_left _ _)
  have hepsilonBudget : epsilon < a0 / (4 * (B + 1)) :=
    lt_of_lt_of_le hepsilonSmall (min_le_right _ _)
  have hbase : (1 / 2 : ℝ) ≤ 1 - epsilon := by linarith
  have hcube : (1 / 4 : ℝ) ^ 2 ≤ (1 - epsilon) ^ 3 := by
    calc
      (1 / 4 : ℝ) ^ 2 ≤ (1 / 2 : ℝ) ^ 3 := by norm_num
      _ ≤ (1 - epsilon) ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hbase 3
  have hroot : (1 / 4 : ℝ) ≤ Real.sqrt ((1 - epsilon) ^ 3) :=
    (Real.le_sqrt (by norm_num) (by positivity)).2 hcube
  have hbudgetProduct : epsilon * (4 * (B + 1)) < a0 :=
    (lt_div_iff₀ (by positivity : 0 < 4 * (B + 1))).1 hepsilonBudget
  have hbudget : B + 1 ≤ a0 / (4 * epsilon) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * epsilon)).2
    nlinarith [hbudgetProduct]
  have hbudgetRoot : B + 1 ≤ Real.sqrt ((1 - epsilon) ^ 3) * (a0 * epsilon⁻¹) := by
    have haeps : 0 < a0 * epsilon⁻¹ := mul_pos ha0 (inv_pos.mpr hepsilon)
    calc
      B + 1 ≤ a0 / (4 * epsilon) := hbudget
      _ = (1 / 4) * (a0 * epsilon⁻¹) := by field_simp
      _ ≤ Real.sqrt ((1 - epsilon) ^ 3) * (a0 * epsilon⁻¹) :=
        mul_le_mul_of_nonneg_right hroot haeps.le
  have hreal : S.scale ^ 3 * (B + 1) ≤
      (S.scale ^ 3 * Real.sqrt ((1 - epsilon) ^ 3)) * (a0 * epsilon⁻¹) := by
    calc
      S.scale ^ 3 * (B + 1) ≤
          S.scale ^ 3 * (Real.sqrt ((1 - epsilon) ^ 3) * (a0 * epsilon⁻¹)) :=
        mul_le_mul_of_nonneg_left hbudgetRoot (pow_nonneg
          (le_of_lt (MorganTianLib.epsilonNeck_scale_pos_and_metric_normalization S).1) 3)
      _ = (S.scale ^ 3 * Real.sqrt ((1 - epsilon) ^ 3)) * (a0 * epsilon⁻¹) := by ring
  let s : Set (MorganTianLib.epsilonNeckDomain epsilon) :=
    {p | -epsilon⁻¹ / 2 < p.1.2 0 ∧ p.1.2 0 < -epsilon⁻¹ / 4}
  have hcoord : Continuous (fun p : MorganTianLib.epsilonNeckDomain epsilon => p.1.2 0) := by
    fun_prop
  have hleft : IsOpen {p : MorganTianLib.epsilonNeckDomain epsilon |
      -epsilon⁻¹ / 2 < p.1.2 0} :=
    isOpen_lt continuous_const hcoord
  have hright : IsOpen {p : MorganTianLib.epsilonNeckDomain epsilon |
      p.1.2 0 < -epsilon⁻¹ / 4} :=
    isOpen_lt hcoord continuous_const
  have hs : MeasurableSet s := by
    dsimp [s]
    rw [Set.setOf_and]
    exact hleft.measurableSet.inter hright.measurableSet
  have href := hround epsilon hepsilon S.referenceMetric S.reference_is_round
  have hscale : 0 < S.scale :=
    (MorganTianLib.epsilonNeck_scale_pos_and_metric_normalization S).1
  letI := M.smooth
  letI : Nonempty (MorganTianLib.epsilonNeckDomain epsilon) :=
    ⟨S.phi.symm (Classical.choice (inferInstance : Nonempty M))⟩
  have hcomparison := (MorganTianLib.epsilonNeck_volume_comparison
    (MeasureTheory.volume : MeasureTheory.Measure
      (EuclideanSpace ℝ (Fin (2 + 1)))) S hs).1
  calc
    ENNReal.ofReal (S.scale ^ 3 * (B + 1)) ≤
        ENNReal.ofReal ((S.scale ^ 3 * Real.sqrt ((1 - epsilon) ^ 3)) *
          (a0 * epsilon⁻¹)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (S.scale ^ 3 * Real.sqrt ((1 - epsilon) ^ 3)) *
        ENNReal.ofReal (a0 * epsilon⁻¹) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hscale.le 3)
        (Real.sqrt_nonneg _))]
    _ ≤ ENNReal.ofReal (S.scale ^ 3 * Real.sqrt ((1 - epsilon) ^ 3)) *
        MorganTianLib.riemannianMeasure S.referenceMetric MeasureTheory.volume s :=
      mul_le_mul_of_nonneg_left href zero_le
    _ ≤ MorganTianLib.riemannianMeasure g MeasureTheory.volume (S.phi '' s) :=
      hcomparison
    _ = regionMeasure g (neckRemovedRegion S) := by
      rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedUniformNeckAllowance
