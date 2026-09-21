import MorganTianLib.Ch02.NeckVolume.RoundDensityPositive
import MorganTianLib.Ch02.NeckVolume.RoundDensityIdentification
import MorganTianLib.Ch02.NeckVolume.RoundHaarBox
import MorganTianLib.Ch02.NeckVolume.RoundCoordinates

open Set MeasureTheory Riemannian Filter
open scoped ContDiff Manifold Topology ENNReal Bundle
noncomputable section
namespace MorganTianLib

/-- **Math.** A fixed axial fraction of a round reference cylinder has positive
volume proportional to its length, uniformly over neck lengths and metrics. -/
theorem roundCylinder_fractional_region_volume_lower
    (mu : Measure (EuclideanSpace ℝ (Fin (2 + 1)))) [mu.IsAddHaarMeasure]
    (sphere0 : EpsilonNeckSphere) :
    ∃ a0 : ℝ, 0 < a0 ∧ ∀ (epsilon : ℝ) (hepsilon : 0 < epsilon)
      (g0 : RiemannianMetric EpsilonNeckCylinderModel (epsilonNeckDomain epsilon)),
      IsRoundCylinderMetric epsilon g0 →
      letI : Nonempty (epsilonNeckDomain epsilon) :=
        ⟨⟨(sphere0, 0), by constructor <;> simpa using inv_pos.mpr hepsilon⟩⟩
      ENNReal.ofReal (a0 * epsilon⁻¹) ≤
        riemannianMeasure (I := EpsilonNeckCylinderModel) g0 mu
          {p | -(epsilon⁻¹) / 2 < p.1.2 0 ∧ p.1.2 0 < -(epsilon⁻¹) / 4} := by
/- SWARM_PROOF_BEGIN -/
  obtain ⟨hcont, hpos⟩ := roundCylinderCoordinateDensity_continuous_pos sphere0
  let u0 := extChartAt (𝓡 2) sphere0 sphere0
  have hu0 : u0 ∈ (extChartAt (𝓡 2) sphere0).target := mem_extChartAt_target sphere0
  let c := roundCylinderCoordinateDensity sphere0 u0 / 2
  have hc : 0 < c := half_pos (hpos u0 hu0)
  have hcu : c < roundCylinderCoordinateDensity sphere0 u0 := by exact half_lt_self (hpos u0 hu0)
  have hct := hcont.continuousAt ((isOpen_extChartAt_target sphere0).mem_nhds hu0)
  have hn : (extChartAt (𝓡 2) sphere0).target ∩
      {u | c < roundCylinderCoordinateDensity sphere0 u} ∈ 𝓝 u0 :=
    inter_mem ((isOpen_extChartAt_target sphere0).mem_nhds hu0)
      (hct (isOpen_Ioi.mem_nhds hcu))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let U := Metric.ball u0 r
  have hU : IsOpen U := Metric.isOpen_ball
  have hUne : U.Nonempty := ⟨u0, Metric.mem_ball_self hr⟩
  obtain ⟨b, hb, hbox⟩ := haar_cylinder_box_volume_lower mu hU hUne Metric.isBounded_ball
  refine ⟨c * b, mul_pos hc hb, ?_⟩
  intro epsilon hepsilon g0 hround
  let a : epsilonNeckDomain epsilon :=
    ⟨(sphere0, 0), by constructor <;> simpa using inv_pos.mpr hepsilon⟩
  letI : Nonempty (epsilonNeckDomain epsilon) := ⟨a⟩
  let Q := epsilonNeckModelEquiv ''
    (U ×ˢ {t : EpsilonNeckAxis | -(epsilon⁻¹) / 2 < t 0 ∧ t 0 < -(epsilon⁻¹) / 4})
  have hinterval : IsOpen {t : EpsilonNeckAxis |
      -(epsilon⁻¹) / 2 < t 0 ∧ t 0 < -(epsilon⁻¹) / 4} := by
    have ht : Continuous (fun t : EpsilonNeckAxis => t 0) :=
      PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0
    exact (isOpen_lt continuous_const ht).inter (isOpen_lt ht continuous_const)
  have hQ : IsOpen Q := epsilonNeckModelEquiv.toHomeomorph.isOpenMap _ (hU.prod hinterval)
  have hdata : ∀ z ∈ Q, z ∈ (extChartAt EpsilonNeckCylinderModel a).target ∧
      c ≤ chartVolumeDensity (I := EpsilonNeckCylinderModel) g0 a z := by
    rintro z ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
    have hfull : -epsilon⁻¹ < t 0 ∧ t 0 < epsilon⁻¹ := by
      constructor <;> linarith [inv_pos.mpr hepsilon, ht.1, ht.2]
    have hid := roundCylinder_chartVolumeDensity_eq_coordinateDensity sphere0 epsilon
      hepsilon g0 hround u (hball hu).1 t hfull
    refine ⟨hid.1, ?_⟩
    rw [hid.2]
    exact (hball hu).2.le
  let V := (extChartAt EpsilonNeckCylinderModel a).source ∩
    (extChartAt EpsilonNeckCylinderModel a) ⁻¹' Q
  have hV : IsOpen V :=
    (continuousOn_extChartAt (I := EpsilonNeckCylinderModel) a).isOpen_inter_preimage
      (isOpen_extChartAt_source a) hQ
  have hpre : chartPreimage (I := EpsilonNeckCylinderModel) a V = Q := by
    ext z
    constructor
    · rintro ⟨⟨hsource, hq⟩, htarget⟩
      simpa only [Set.mem_preimage, (extChartAt EpsilonNeckCylinderModel a).right_inv htarget] using hq
    · intro hq
      have ht := (hdata z hq).1
      refine ⟨⟨(extChartAt EpsilonNeckCylinderModel a).map_target ht, ?_⟩, ht⟩
      simpa only [Set.mem_preimage, (extChartAt EpsilonNeckCylinderModel a).right_inv ht] using hq
  have hsub : V ⊆ {p : epsilonNeckDomain epsilon |
      -(epsilon⁻¹) / 2 < p.1.2 0 ∧ p.1.2 0 < -(epsilon⁻¹) / 4} := by
    rintro p ⟨hp, ⟨⟨u, t⟩, ⟨hu, ht⟩, hz⟩⟩
    have heq := roundCylinder_extChartAt_apply epsilon a p
    have haxis : p.1.2 = t :=
      congrArg Prod.snd (epsilonNeckModelEquiv.injective (heq.symm.trans hz.symm))
    simpa only [Set.mem_setOf_eq, haxis] using ht
  have hlocal : riemannianMeasure (I := EpsilonNeckCylinderModel) g0 mu V =
      ∫⁻ z in Q, ENNReal.ofReal
        (chartVolumeDensity (I := EpsilonNeckCylinderModel) g0 a z) ∂mu := by
    rw [riemannianMeasure_apply_chart mu g0 a hV.measurableSet inter_subset_left, hpre]
  calc
    ENNReal.ofReal (c * b * epsilon⁻¹) =
        ENNReal.ofReal c * ENNReal.ofReal (b * epsilon⁻¹) := by
      rw [← ENNReal.ofReal_mul hc.le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal c * mu Q :=
      mul_le_mul_right (hbox epsilon⁻¹ (inv_pos.mpr hepsilon)) _
    _ = ∫⁻ z in Q, ENNReal.ofReal c ∂mu := by simp
    _ ≤ ∫⁻ z in Q, ENNReal.ofReal
        (chartVolumeDensity (I := EpsilonNeckCylinderModel) g0 a z) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hQ.measurableSet] with z hz
      exact ENNReal.ofReal_le_ofReal (hdata z hz).2
    _ = riemannianMeasure (I := EpsilonNeckCylinderModel) g0 mu V := hlocal.symm
    _ ≤ _ := measure_mono hsub
/- SWARM_PROOF_END -/

end MorganTianLib
