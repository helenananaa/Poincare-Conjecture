import PoincareConjecture.ProofContract.Refinement20260927.MetricInitialization
import MorganTianLib.Ch03.RicciFlow.CompactVolumeScalarLower
import MorganTianLib.Ch04.ScalarMinimumFlow
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory Riemannian MorganTianLib
open CriticalPath.SurgeryBudget
open scoped Topology Manifold ContDiff ENNReal
local instance : NeZero (Module.finrank ℝ Euclidean3) := ⟨by simp [Euclidean3]⟩
/-- **Math.** May be disconnected: one smooth stage can contain several components. -/
structure CompactSmoothThree extends TopCat.{u} where
  hausdorff : T2Space toTopCat
  compact : CompactSpace toTopCat
  secondCountable : SecondCountableTopology toTopCat
  nonempty : Nonempty toTopCat
  charts : ChartedSpace Euclidean3 toTopCat
  smooth : @IsManifold ℝ _ Euclidean3 _ _ Euclidean3 _ (𝓡 3) ∞ toTopCat _ charts
instance : CoeSort CompactSmoothThree.{u} (Type u) := ⟨fun M => M.toTopCat⟩
instance (M : CompactSmoothThree) : TopologicalSpace M := M.toTopCat.str
instance (M : CompactSmoothThree) : T2Space M := M.hausdorff
instance (M : CompactSmoothThree) : CompactSpace M := M.compact
instance (M : CompactSmoothThree) : SecondCountableTopology M := M.secondCountable
instance (M : CompactSmoothThree) : Nonempty M := M.nonempty
instance (M : CompactSmoothThree) : ChartedSpace Euclidean3 M := M.charts
instance (M : CompactSmoothThree) : IsManifold (𝓡 3) ∞ M := M.smooth
instance (M : CompactSmoothThree) : MeasurableSpace M := borel M
instance (M : CompactSmoothThree) : BorelSpace M := ⟨rfl⟩
/-- **Math.** An endpoint-inclusive propagation goal for the actual Ricci equation.
The existing half-open minimum theorem is not silently applied at T. -/
def ClosedScalarPropagationStatement : Prop :=
  ∀ (M : CompactSmoothThree.{u}) (g : ℝ → Riemannian.RiemannianMetric (𝓡 3) M)
    (T C : ℝ), 0 < T → 0 ≤ C → IsRicciFlowOn g (Icc 0 T) →
    (∀ p : M, -C ≤ scalarCurvatureAt (g 0) (g 0).leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita (g 0)) p) →
    ∀ t ∈ Icc (0 : ℝ) T, ∀ p : M,
      -C ≤ scalarCurvatureAt (g t) (g t).leviCivitaConnection
        (canonicalLeviCivita_isLeviCivita (g t)) p
/-- **Math.** Actual Riemannian measure, not a free volume parameter. -/
abbrev actualMetricMeasure {M : CompactSmoothThree.{u}}
    (g : Riemannian.RiemannianMetric (𝓡 3) M) : Measure M :=
  riemannianMeasure (I := 𝓡 3) g (volume : Measure Euclidean3)
/-- **Math.** A real smooth Ricci interval identifies BOTH measures with the
recorded slices. The required growth inequality is not a field. -/
structure RicciIntervalBridge (X Y : MeasuredSlice.{u}) (C T : ℝ) where
  space : CompactSmoothThree.{u}
  metric : ℝ → Riemannian.RiemannianMetric (𝓡 3) space
  duration_pos : 0 < T
  flow : IsRicciFlowOn metric (Icc 0 T)
  initial_scalar : ∀ p : space, -C ≤ scalarCurvatureAt (metric 0)
    (metric 0).leviCivitaConnection (canonicalLeviCivita_isLeviCivita (metric 0)) p
  start : X ≃ᵐ space
  finish : Y ≃ᵐ space
  start_preserves : MeasurePreserving start X.measure (actualMetricMeasure (metric 0))
  finish_preserves : MeasurePreserving finish Y.measure (actualMetricMeasure (metric T))
/-- **Math.** Derive the budget's smooth-growth field from the actual Ricci PDE. -/
theorem ricci_interval_volume_growth (propagate : ClosedScalarPropagationStatement.{u})
    {X Y : MeasuredSlice.{u}} {C T : ℝ} (hC : 0 ≤ C)
    (e : RicciIntervalBridge X Y C T) : Y.volume ≤ Real.exp (C*T)*X.volume := by
  have hscalar := propagate e.space e.metric T C e.duration_pos hC e.flow e.initial_scalar
  have growth := (compact_real_volume_upper_of_scalar_lower (volume : Measure Euclidean3)
    e.flow hscalar MeasurableSet.univ (show T ∈ Icc (0:ℝ) T from ⟨e.duration_pos.le,le_rfl⟩)).2
  have hx : X.measure univ = actualMetricMeasure (e.metric 0) univ := by
    simpa using e.start_preserves.measure_preimage_equiv univ
  have hy : Y.measure univ = actualMetricMeasure (e.metric T) univ := by
    simpa using e.finish_preserves.measure_preimage_equiv univ
  simpa only [MeasuredSlice.volume,hx,hy,actualMetricMeasure] using growth
/-- **Math.** Exact event histories with PDE intervals instead of an assumed
volume-growth inequality. Actual local surgery loss still has to be supplied. -/
structure RicciMeasuredHistory (n : ℕ) (a T delta initialVolume : ℝ)
    (initialComponents : ℕ) where
  pre : ℕ → MeasuredSlice.{u}
  post : ℕ → MeasuredSlice.{u}
  time : ℕ → ℝ
  cuts : ℕ → ℕ
  discards : ℕ → ℕ
  components : ℕ → ℕ
  time_zero : time 0 = 0
  time_mono : Monotone time
  horizon : ∀ i ≤ n, time i ≤ T
  initial_volume : (post 0).volume = initialVolume
  initial_components : components 0 = initialComponents
  evolution : ∀ i < n, Nonempty (RicciIntervalBridge (post i) (pre i) a (time (i+1)-time i))
  replacement : ∀ i < n, MeasuredReplacement (pre i) (post (i+1)) (cuts i)
  local_loss : ∀ i (hi : i < n) (j : Fin (cuts i)),
    delta + ((post (i+1)).measure ((replacement i hi).new (some j))).toReal ≤
      ((pre i).measure ((replacement i hi).old (some j))).toReal
  component_step : ∀ i < n, components (i+1) + discards i ≤ components i + cuts i
  event_active : ∀ i < n, 1 ≤ cuts i + discards i
/-- **Math.** The formerly assumed growth field is constructed here. -/
def RicciMeasuredHistory.toMeasured (propagate : ClosedScalarPropagationStatement.{u})
    {n c : ℕ} {a T delta V : ℝ} (ha : 0 ≤ a)
    (h : RicciMeasuredHistory.{u} n a T delta V c) :
    MeasuredSurgeryHistory.{u} n a T delta V c where
  pre := h.pre
  post := h.post
  time := h.time
  cuts := h.cuts
  discards := h.discards
  components := h.components
  time_zero := h.time_zero
  time_mono := h.time_mono
  horizon := h.horizon
  initial_volume := h.initial_volume
  initial_components := h.initial_components
  smooth_growth := fun i hi => ricci_interval_volume_growth propagate ha
    (Classical.choice (h.evolution i hi))
  replacement := h.replacement
  local_loss := h.local_loss
  component_step := h.component_step
  event_active := h.event_active
/-- **Math.** Distinct sampled times require at least as many recorded events. -/
theorem sampled_times_card_le (n : ℕ) (time : ℕ → ℝ) (s : Finset ℝ)
    (hc : ∀ t ∈ s, ∃ i : Fin n, time (i.val+1) = t) : s.card ≤ n := by
  classical
  let f : Fin n → ℝ := fun i => time (i.val+1)
  have hs : s ⊆ Finset.univ.image f := by
    intro t ht
    obtain ⟨i,hi⟩ := hc t ht
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
  exact (Finset.card_le_card hs).trans (by simpa using Finset.card_image_le (f := f) (s := Finset.univ))
/-- **Math.** The initial metric supplies an actual finite measured slice. -/
def initialMetricSlice (M : ClosedThreeManifold.{u}) [IsSmooth M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) : MeasuredSlice.{u} := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  let mu : Measure M := riemannianMeasure (I := 𝓡 3) g (volume : Measure Euclidean3)
  have hf : mu univ < ⊤ := riemannianMeasure_lt_top_of_isCompact
    (volume : Measure Euclidean3) g isCompact_univ
  exact ⟨M,inferInstance,mu,⟨hf⟩⟩
/-- **Math.** All finite samples refer to the SAME event set and initial metric measure.
No event finiteness and no smooth volume growth is assumed here. -/
def AnchoredRicciBudget (M : ClosedThreeManifold.{u}) [IsSmooth M]
    (d : MetricInitialData M) (T : ℝ) (E : Set ℝ) : Prop :=
  ∃ a delta : ℝ, d.scalarConstant ≤ a ∧ 0 < delta ∧
    ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ E →
      ∃ n : ℕ, ∃ h : RicciMeasuredHistory.{u} n a T delta (initialMetricSlice M d.metric).volume 1,
        h.post 0 = initialMetricSlice M d.metric ∧
        ∀ t ∈ s, ∃ i : Fin n, h.time (i.val+1) = t
theorem anchored_budget_to_uniform (propagate : ClosedScalarPropagationStatement.{u})
    (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M)
    {T : ℝ} {E : Set ℝ} (h : AnchoredRicciBudget M d T E) : UniformEventBudget.{u} T E := by
  obtain ⟨a,delta,ha,hd,hcover⟩ := h
  have ha0 : 0 ≤ a := d.scalarConstant_nonneg.trans ha
  refine ⟨a,delta,(initialMetricSlice M d.metric).volume,1,ha0,hd,?_⟩
  intro s hs
  obtain ⟨n,h,_hstart,hcover⟩ := hcover s hs
  exact ⟨n,sampled_times_card_le n h.time s hcover,⟨h.toMeasured propagate ha0⟩⟩
/-- **Math.** Still RESEARCH: build the actual intervals, local surgery loss,
finite-sample coverage and empty end for the same projected event set.
The full metric/PDE-to-topological-history correspondence is NOT claimed frozen. -/
def RicciBudgetGeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M →
    ∃ H : RelabeledProjection checked_side_atlas checked_negative_collar M,
      H.pre H.horizon = [] ∧ AnchoredRicciBudget M d H.horizon H.events
theorem geometric_of_ricci_budget_producer (propagate : ClosedScalarPropagationStatement.{u})
    (producer : RicciBudgetGeometryProducerStatement.{u}) : GeometricTraceStatement.{u} := by
  intro M hsm hsc
  letI : IsSmooth M := hsm
  obtain ⟨d⟩ := metric_initialData_exists M
  obtain ⟨H,hend,hbudget⟩ := producer M d hsc
  exact checked_projection_trace H hend (anchored_budget_to_uniform propagate M d hbudget)
theorem public_of_ricci_budget_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (propagate : ClosedScalarPropagationStatement.{u})
    (geometry : RicciBudgetGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  Proofs.topological_of_two_contracts
    (smoothing_of_finitePL_producers triangulate (finitePLAtlasProducer_iff.mp atlas))
    (geometric_of_ricci_budget_producer propagate geometry)
#print axioms ricci_interval_volume_growth
#print axioms RicciMeasuredHistory.toMeasured
#print axioms sampled_times_card_le
#print axioms initialMetricSlice
#print axioms anchored_budget_to_uniform
#print axioms geometric_of_ricci_budget_producer
#print axioms public_of_ricci_budget_frontier
end PoincareConjecture.ProofContract.Refinement20260927
