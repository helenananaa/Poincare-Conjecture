import MorganTianLib.Ch02.GreenIdentity
import MorganTianLib.Ch01.RiemannianMeasure

open Set MeasureTheory Filter
open scoped ContDiff Manifold Topology ENNReal
noncomputable section
namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

/-- **Math.** Every nonempty open region has positive canonical Riemannian volume. -/
theorem riemannianMeasure_pos_of_nonempty_isOpen
    (mu : Measure E) [mu.IsAddHaarMeasure] (g : RiemannianMetric I M)
    {U : Set M} (hU : IsOpen U) (hUne : U.Nonempty) :
    0 < riemannianMeasure (I := I) g mu U := by
  obtain ⟨p, hp⟩ := hUne
  let V : Set M := U ∩ (extChartAt I p).source
  have hV : IsOpen V := hU.inter (isOpen_extChartAt_source p)
  have hpV : p ∈ V := ⟨hp, mem_extChartAt_source p⟩
  let Q : Set E := chartPreimage (I := I) p V
  have hQ : IsOpen Q := by
    simpa [Q, chartPreimage, inter_comm] using
      (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
        (isOpen_extChartAt_target p) hV
  have hQne : Q.Nonempty := by
    refine ⟨extChartAt I p p, ?_⟩
    constructor
    · simpa only [Set.mem_preimage, (extChartAt I p).left_inv (mem_extChartAt_source p)] using hpV
    · exact mem_extChartAt_target p
  have hQpos : 0 < mu Q := hQ.measure_pos mu hQne
  have hf : AEMeasurable
      (fun y : E => ENNReal.ofReal (chartVolumeDensity (I := I) g p y)) (mu.restrict Q) := by
    exact (ENNReal.continuous_ofReal.comp_continuousOn
      ((contDiffOn_chartVolumeDensity (I := I) g p).continuousOn.mono
        (chartPreimage_subset_target p V))).aemeasurable hQ.measurableSet
  have hlocal : 0 < riemannianMeasure (I := I) g mu V := by
    rw [riemannianMeasure_apply_chart mu g p hV.measurableSet inter_subset_right]
    change 0 < ∫⁻ y in Q, ENNReal.ofReal (chartVolumeDensity (I := I) g p y) ∂mu
    apply pos_iff_ne_zero.mpr
    intro hzero
    have hz := (setLIntegral_eq_zero_iff' hQ.measurableSet hf).mp hzero
    have hnull : ∀ᵐ y ∂mu, y ∉ Q := hz.mono (fun y hy hmem => by
      have hpos := ENNReal.ofReal_pos.mpr (chartVolumeDensity_pos g p hmem.2)
      exact (ne_of_gt hpos) (hy hmem))
    have hmu : mu Q = 0 := by simpa [ae_iff] using hnull
    exact (ne_of_gt hQpos) hmu
  exact hlocal.trans_le (measure_mono inter_subset_left)

/-- **Math.** The canonical Riemannian measure is locally finite. -/
theorem riemannianMeasure_isLocallyFinite
    (mu : Measure E) [mu.IsAddHaarMeasure] (g : RiemannianMetric I M) :
    IsLocallyFiniteMeasure (riemannianMeasure (I := I) g mu) := by
  constructor
  intro p
  let q : E := extChartAt I p p
  let rho : E → ℝ := chartVolumeDensity (I := I) g p
  let B : ℝ := rho q + 1
  obtain ⟨W, hqW, hW, hmuW⟩ := mu.exists_isOpen_measure_lt_top q
  let O : Set E := W ∩ ((extChartAt I p).target ∩ rho ⁻¹' Iio B)
  have hO : IsOpen O := hW.inter
    ((contDiffOn_chartVolumeDensity (I := I) g p).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target p) isOpen_Iio)
  have hqO : q ∈ O := ⟨hqW, mem_extChartAt_target p, by change rho q < rho q + 1; linarith⟩
  have hOtarget : O ⊆ (extChartAt I p).target := fun _ h => h.2.1
  have hmuO : mu O < ⊤ := (measure_mono inter_subset_left).trans_lt hmuW
  let V : Set M := (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' O
  have hV : IsOpen V := (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage
    (isOpen_extChartAt_source p) hO
  have hpV : p ∈ V := ⟨mem_extChartAt_source p, hqO⟩
  have hpre : chartPreimage (I := I) p V = O := by
    ext y
    constructor
    · intro hy
      have h := hy.1.2
      simpa only [Set.mem_preimage, (extChartAt I p).right_inv hy.2] using h
    · intro hy
      exact ⟨⟨(extChartAt I p).map_target (hOtarget hy), by
        simpa only [Set.mem_preimage, (extChartAt I p).right_inv (hOtarget hy)] using hy⟩, hOtarget hy⟩
  have hfinite : riemannianMeasure (I := I) g mu V < ⊤ := by
    rw [riemannianMeasure_apply_chart mu g p hV.measurableSet inter_subset_left, hpre]
    have hle : (∫⁻ y in O, ENNReal.ofReal (rho y) ∂mu) ≤
        ∫⁻ y in O, ENNReal.ofReal B ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hO.measurableSet] with y hy
      exact ENNReal.ofReal_le_ofReal (le_of_lt hy.2.2)
    apply hle.trans_lt
    simpa only [lintegral_const, Measure.restrict_apply_univ] using
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmuO
  exact ⟨V, hV.mem_nhds hpV, hfinite⟩

/-- **Math.** Compact metric regions have finite canonical Riemannian volume. -/
theorem riemannianMeasure_lt_top_of_isCompact
    (mu : Measure E) [mu.IsAddHaarMeasure] (g : RiemannianMetric I M)
    {K : Set M} (hK : IsCompact K) : riemannianMeasure (I := I) g mu K < ⊤ := by
  letI := riemannianMeasure_isLocallyFinite mu g
  exact hK.measure_lt_top

end MorganTianLib
