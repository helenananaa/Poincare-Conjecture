import PoincareConjecture.ProofContract.Refinement20260927.CompactMetricComparison
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1 MeasureTheory
open scoped Topology
/-- **Math.** Compact coordinate parameter space, not a global tangent frame. -/
structure CompactCoefficientSpace where
  carrier : Type u
  metric : MetricSpace carrier
  compact : letI : MetricSpace carrier := metric; CompactSpace carrier
  nonempty : Nonempty carrier
instance (K : CompactCoefficientSpace.{u}) : MetricSpace K.carrier := K.metric
instance (K : CompactCoefficientSpace.{u}) : CompactSpace K.carrier := K.compact
instance (K : CompactCoefficientSpace.{u}) : Nonempty K.carrier := K.nonempty
/-- **Math.** A fixed quadratic integral realization of the SAME spectrum.
The measure, base maps and vector fields do not change with time. Actual manifold
Dirichlet energy and its chart/trivialization construction remain research. -/
structure QuadraticEnergyRepresentation (F : SweepoutSpectrum.{u}) (a b : ℝ) where
  coefficients : CompactCoefficientSpace.{u}
  Q : ℝ × coefficients.carrier → MetricOperator
  continuous : ContinuousOn Q (Icc a b ×ˢ univ)
  positive : ∀ t ∈ Icc a b, ∀ x v, v ≠ 0 → 0 < quadraticValue (Q (t,x)) v
  domain : Type u
  measurable : MeasurableSpace domain
  measure : @Measure domain measurable
  base : F.index → SweepParameter → domain → coefficients.carrier
  vector : F.index → SweepParameter → domain → Euclidean3
  integrable : letI : MeasurableSpace domain := measurable
    ∀ i x t, t ∈ Icc a b → Integrable
      (fun z => quadraticValue (Q (t,base i x z)) (vector i x z)) measure
  energy_eq : letI : MeasurableSpace domain := measurable
    ∀ i x t, t ∈ Icc a b → F.energy i t x =
      ∫ z, quadraticValue (Q (t,base i x z)) (vector i x z) ∂measure
/-- **Math.** One radius controls all sweepouts/slices, without their individual
energy or derivative bounds being uniform. It comes from the common tensor. -/
theorem energy_relative_comparison (coercive : CompactQuadraticLowerStatement.{u})
    (timeUniform : CompactMetricTimeVariationStatement.{u}) {F : SweepoutSpectrum.{u}}
    {a b t eta : ℝ} (hab : a ≤ b) (d : QuadraticEnergyRepresentation F a b)
    (ht : t ∈ Icc a b) (he : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Icc a b, dist s t < r → ∀ i x,
      (1-eta)*F.energy i t x ≤ F.energy i s x ∧
      F.energy i s x ≤ (1+eta)*F.energy i t x := by
  letI : MeasurableSpace d.domain := d.measurable
  obtain ⟨r,hr,hcompare⟩ := compact_metric_relative coercive timeUniform
    d.coefficients.carrier d.Q hab d.continuous d.positive ht he
  refine ⟨r,hr,?_⟩
  intro s hs hst i x
  rw [d.energy_eq i x t ht,d.energy_eq i x s hs]
  have hlow := integral_mono ((d.integrable i x t ht).const_mul (1-eta))
    (d.integrable i x s hs) (fun z => (hcompare s hs hst (d.base i x z) (d.vector i x z)).1)
  have hupp := integral_mono (d.integrable i x s hs)
    ((d.integrable i x t ht).const_mul (1+eta))
    (fun z => (hcompare s hs hst (d.base i x z) (d.vector i x z)).2)
  simpa only [integral_const_mul] using And.intro hlow hupp
/-- **Math.** Order-level inf-sup comparison, without an attained optimum or a
chosen minimizing sequence. Both factors must be strictly positive. -/
theorem width_sandwich (F : SweepoutSpectrum.{u}) (s t l h : ℝ)
    (hl : 0 < l) (hh : 0 < h)
    (he : ∀ i x, l*F.energy i t x ≤ F.energy i s x ∧ F.energy i s x ≤ h*F.energy i t x) :
    l*F.width t ≤ F.width s ∧ F.width s ≤ h*F.width t := by
  have hpeakU (i : F.index) : F.peak i s ≤ h*F.peak i t := by
    apply csSup_le (range_nonempty _)
    rintro _ ⟨x,rfl⟩
    exact (he i x).2.trans (mul_le_mul_of_nonneg_left (F.energy_le_peak i t x) hh.le)
  have hpeakL (i : F.index) : l*F.peak i t ≤ F.peak i s := by
    have hd : F.peak i t ≤ F.peak i s / l := by
      apply csSup_le (range_nonempty _)
      rintro _ ⟨x,rfl⟩
      apply (le_div_iff₀ hl).mpr
      simpa only [mul_comm] using (he i x).1.trans (F.energy_le_peak i s x)
    simpa only [mul_comm] using (le_div_iff₀ hl).mp hd
  constructor
  · apply le_csInf (range_nonempty _)
    rintro _ ⟨i,rfl⟩
    exact (mul_le_mul_of_nonneg_left (F.width_le_peak i t) hl.le).trans (hpeakL i)
  · have hd : F.width s / h ≤ F.width t := by
      apply le_csInf (range_nonempty _)
      rintro _ ⟨i,rfl⟩
      apply (div_le_iff₀ hh).mpr
      simpa only [mul_comm] using (F.width_le_peak i s).trans (hpeakU i)
    simpa only [mul_comm] using (div_le_iff₀ hh).mp hd
/-- **Math.** Width continuity follows from the fixed integral representation
and actual compact metric variation; it is not part of that representation. -/
theorem width_continuous_of_quadratic_energy (coercive : CompactQuadraticLowerStatement.{u})
    (timeUniform : CompactMetricTimeVariationStatement.{u}) {F : SweepoutSpectrum.{u}}
    {a b : ℝ} (hab : a ≤ b) (d : QuadraticEnergyRepresentation F a b) :
    ContinuousOn F.width (Icc a b) := by
  intro t ht
  apply Metric.continuousWithinAt_iff.mpr
  intro e he
  let eta := min (1/2 : ℝ) (e/(F.width t+1))
  have hw := F.width_nonneg t
  have heta : 0 < eta := lt_min (by norm_num) (div_pos he (by linarith))
  have heta1 : eta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hcost : eta * F.width t < e := by
    have h := (le_div_iff₀ (show 0 < F.width t+1 by linarith)).mp
      (min_le_right (1/2 : ℝ) (e/(F.width t+1)))
    change eta*(F.width t+1) ≤ e at h
    nlinarith
  obtain ⟨r,hr,hcompare⟩ := energy_relative_comparison coercive timeUniform hab d ht heta
  refine ⟨r,hr,?_⟩
  intro s hs hst
  have hbounds := width_sandwich F s t (1-eta) (1+eta) (by linarith) (by linarith)
    (hcompare s hs hst)
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith [hbounds.1,hbounds.2,hcost]
#print axioms energy_relative_comparison
#print axioms width_sandwich
#print axioms width_continuous_of_quadratic_energy
end PoincareConjecture.ProofContract.Refinement20260927
