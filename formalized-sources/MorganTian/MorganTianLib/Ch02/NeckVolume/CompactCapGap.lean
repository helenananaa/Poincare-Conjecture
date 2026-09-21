import MorganTianLib.Ch02.NeckVolume.ActualVolumeComparison
import MorganTianLib.Ch02.NeckVolume.RoundReferenceLower
import MorganTianLib.Ch01.RiemannianMeasureRegularity
import MorganTianLib.Ch01.MetricRescaling

open Set MeasureTheory Riemannian
open scoped ContDiff Manifold Topology ENNReal Bundle
noncomputable section
namespace MorganTianLib
local notation "E3" => EuclideanSpace ℝ (Fin (2 + 1))
variable {H Hc : Type*} [TopologicalSpace H] [TopologicalSpace Hc]
  {I : ModelWithCorners ℝ E3 H} {J : ModelWithCorners ℝ E3 Hc}
  [I.Boundaryless] [J.Boundaryless]
  {N C : Type*} [TopologicalSpace N] [TopologicalSpace C]
  [ChartedSpace H N] [ChartedSpace Hc C] [IsManifold I ∞ N] [IsManifold J ∞ C]
  [MeasurableSpace N] [BorelSpace N] [MeasurableSpace C] [BorelSpace C]
  [SecondCountableTopology N] [SecondCountableTopology C] [Nonempty N] [Nonempty C]
  [SigmaCompactSpace N] [T2Space N] [T2Space C]

/-- **Math.** A sufficiently long epsilon-neck region dominates any fixed compact cap metric
at the same scale, with at least one scale-cubed of volume left over. This is a volume
comparison only: it does not assert smooth gluing or curvature control for a surgery cap. -/
theorem epsilonNeck_volume_dominates_fixed_compact_cap
    (mu : Measure E3) [mu.IsAddHaarMeasure] (sphere0 : EpsilonNeckSphere)
    (gcap : RiemannianMetric J C) {K : Set C} (hK : IsCompact K) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ {epsilon : ℝ}, 0 < epsilon → epsilon < epsilon0 →
      ∀ {g : RiemannianMetric I N} {x : N} (S : EpsilonNeckStructure epsilon g x),
        ENNReal.ofReal (S.scale ^ 3) +
          riemannianMeasure (I := J)
            (rescaledMetric gcap (S.scale ^ 2)
              (sq_pos_of_pos (epsilonNeck_scale_pos_and_metric_normalization S).1)) mu K ≤
          riemannianMeasure (I := I) g mu
            (S.phi '' {p : epsilonNeckDomain epsilon |
              -(epsilon⁻¹) / 2 < p.1.2 0 ∧ p.1.2 0 < -(epsilon⁻¹) / 4}) := by
/- SWARM_PROOF_BEGIN -/
  letI : LocallyCompactSpace Hc := J.locallyCompactSpace
  letI : LocallyCompactSpace C := ChartedSpace.locallyCompactSpace Hc C
  letI : SigmaCompactSpace C := inferInstance
  obtain ⟨a0, ha0, hroundLower⟩ := roundCylinder_fractional_region_volume_lower mu sphere0
  let V := riemannianMeasure (I := J) gcap mu K
  have hVfinite : V < ⊤ := riemannianMeasure_lt_top_of_isCompact mu gcap hK
  let v : ℝ := V.toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hv1 : 0 < v + 1 := by linarith
  let epsilon0 := min (1 / 2 : ℝ) (a0 / (4 * (v + 1)))
  have he0 : 0 < epsilon0 := lt_min (by norm_num) (div_pos ha0 (mul_pos (by norm_num) hv1))
  refine ⟨epsilon0, he0, ?_⟩
  intro epsilon hepsilon hsmall g x S
  letI : Nonempty (epsilonNeckDomain epsilon) := ⟨S.phi.symm x⟩
  have hehalf : epsilon < 1 / 2 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hecut : epsilon < a0 / (4 * (v + 1)) := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hroot : (1 / 4 : ℝ) ≤ Real.sqrt ((1 - epsilon) ^ 3) := by
    have hp : (1 / 2 : ℝ) ^ 3 ≤ (1 - epsilon) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 3
    have hs := Real.sqrt_le_sqrt (show (1 / 4 : ℝ) ^ 2 ≤ (1 - epsilon) ^ 3 by norm_num at hp ⊢; linarith)
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hs
    exact hs
  have hratio : v + 1 ≤ a0 / (4 * epsilon) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hepsilon)).2
    have h := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hv1)).1 hecut
    nlinarith
  have hscalar : v + 1 ≤ Real.sqrt ((1 - epsilon) ^ 3) * (a0 * epsilon⁻¹) := by
    calc
      v + 1 ≤ a0 / (4 * epsilon) := hratio
      _ = (1 / 4 : ℝ) * (a0 * epsilon⁻¹) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hroot (mul_nonneg ha0.le (inv_nonneg.mpr hepsilon.le))
  have hh : 0 < S.scale := (epsilonNeck_scale_pos_and_metric_normalization S).1
  have hh3 : 0 ≤ S.scale ^ 3 := pow_nonneg hh.le 3
  have hcap : riemannianMeasure (I := J)
      (rescaledMetric gcap (S.scale ^ 2)
        (sq_pos_of_pos (epsilonNeck_scale_pos_and_metric_normalization S).1)) mu K =
      ENNReal.ofReal (S.scale ^ 3) * V := by
    rw [rescaledMetric_riemannianMeasure, Measure.smul_apply, smul_eq_mul]
    have hdim : Module.finrank ℝ E3 = 3 := by simp
    rw [hdim]
    have hp : (S.scale ^ 2) ^ 3 = (S.scale ^ 3) ^ 2 := by ring
    rw [hp, Real.sqrt_sq hh3]
  let A : Set (epsilonNeckDomain epsilon) :=
    {p | -(epsilon⁻¹) / 2 < p.1.2 0 ∧ p.1.2 0 < -(epsilon⁻¹) / 4}
  have hA : IsOpen A := by
    have hc : Continuous (fun p : epsilonNeckDomain epsilon => p.1.2 0) :=
      ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_snd).comp continuous_subtype_val
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hn := (epsilonNeck_volume_comparison mu S hA.measurableSet).1
  have hr := hroundLower epsilon hepsilon S.referenceMetric S.reference_is_round
  have hVo : ENNReal.ofReal v = V := ENNReal.ofReal_toReal hVfinite.ne
  rw [hcap]
  calc
    ENNReal.ofReal (S.scale ^ 3) + ENNReal.ofReal (S.scale ^ 3) * V =
        ENNReal.ofReal (S.scale ^ 3 * (v + 1)) := by
      rw [ENNReal.ofReal_mul hh3, ENNReal.ofReal_add hv (by norm_num), hVo]
      simp only [ENNReal.ofReal_one, mul_add, mul_one]
      ac_rfl
    _ ≤ ENNReal.ofReal (S.scale ^ 3 * (Real.sqrt ((1 - epsilon) ^ 3) * (a0 * epsilon⁻¹))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hscalar hh3)
    _ = ENNReal.ofReal (S.scale ^ 3 * Real.sqrt ((1 - epsilon) ^ 3)) *
        ENNReal.ofReal (a0 * epsilon⁻¹) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hh3 (Real.sqrt_nonneg _))]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (S.scale ^ 3 * Real.sqrt ((1 - epsilon) ^ 3)) *
        riemannianMeasure (I := EpsilonNeckCylinderModel) S.referenceMetric mu A :=
      mul_le_mul_right hr _
    _ ≤ _ := hn
/- SWARM_PROOF_END -/
end MorganTianLib
