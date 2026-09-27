import PoincareConjecture.ProofContract.Refinement20260927.NeckLoss
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open CriticalPath.SurgeryBudget
/-- **Math.** Local loss is not an assumed field; instead require actual neck/cap measure models. -/
structure NeckControlledHistory (n : ℕ) (a T rho B epsilon0 initialVolume : ℝ)
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
  neckModels : ∀ i (hi : i < n) (j : Fin (cuts i)),
    NeckReplacementModel (pre i) (post (i+1))
      ((replacement i hi).old (some j)) ((replacement i hi).new (some j)) B epsilon0 rho
  component_step : ∀ i < n, components (i+1) + discards i ≤ components i + cuts i
  event_active : ∀ i < n, 1 ≤ cuts i + discards i
def NeckControlledHistory.toRicci (scaling : FiniteCapScalingStatement.{u})
    {n c : ℕ} {a T rho B epsilon0 V : ℝ} (hrho : 0 < rho) (hB : 0 ≤ B)
    (allowance : NeckAllowance.{u} B epsilon0)
    (h : NeckControlledHistory.{u} n a T rho B epsilon0 V c) :
    RicciMeasuredHistory.{u} n a T (rho^3) V c where
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
  evolution := h.evolution
  replacement := h.replacement
  local_loss := fun i hi j => neckReplacement_local_loss scaling hB hrho allowance (h.neckModels i hi j)
  component_step := h.component_step
  event_active := h.event_active
/-- **Math.** Uniform constants precede every finite event sample; initial measure is the given metric. -/
def AnchoredNeckBudget (M : ClosedThreeManifold.{u}) [IsSmooth M]
    (d : MetricInitialData M) (B epsilon0 T : ℝ) (E : Set ℝ) : Prop :=
  ∃ a rho : ℝ, d.scalarConstant ≤ a ∧ 0 < rho ∧
    ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ E → ∃ n : ℕ,
      ∃ h : NeckControlledHistory.{u} n a T rho B epsilon0 (initialMetricSlice M d.metric).volume 1,
        h.post 0 = initialMetricSlice M d.metric ∧
        ∀ t ∈ s, ∃ i : Fin n, h.time (i.val+1) = t
theorem anchored_neck_to_ricci (scaling : FiniteCapScalingStatement.{u})
    (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M)
    {B epsilon0 T : ℝ} {E : Set ℝ} (hB : 0 ≤ B) (allowance : NeckAllowance.{u} B epsilon0)
    (h : AnchoredNeckBudget M d B epsilon0 T E) : AnchoredRicciBudget M d T E := by
  obtain ⟨a,rho,ha,hrho,samples⟩ := h
  refine ⟨a,rho^3,ha,pow_pos hrho 3,?_⟩
  intro s hs
  obtain ⟨n,h,hstart,htimes⟩ := samples s hs
  exact ⟨n,h.toRicci scaling hrho hB allowance,hstart,htimes⟩
/-- **Math.** The geometric producer must first bound the TOTAL normalized cap volume,
then handle sufficiently small requested neck accuracy. The real flow/cap existence,
scale lower bound, measure identifications and full topology correspondence remain research. -/
def NeckLossGeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon0 : ℝ, 0 < epsilon0 →
      ∃ H : RelabeledProjection checked_side_atlas checked_negative_collar M,
        H.pre H.horizon = [] ∧ AnchoredNeckBudget M d B epsilon0 H.horizon H.events
theorem ricci_producer_of_neck_loss (allowances : UniformNeckAllowanceStatement.{u})
    (scaling : FiniteCapScalingStatement.{u}) (producer : NeckLossGeometryProducerStatement.{u}) :
    RicciBudgetGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,hB,run⟩ := producer M d hsc
  obtain ⟨epsilon0,heps,allowance⟩ := allowances B hB
  obtain ⟨H,hend,budget⟩ := run epsilon0 heps
  exact ⟨H,hend,anchored_neck_to_ricci scaling M d hB allowance budget⟩
/-- **Math.** The two new volume leaves and three honest research obligations
still return the exact unchanged V1 public target. -/
theorem public_of_neck_loss_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (allowances : UniformNeckAllowanceStatement.{u})
    (scaling : FiniteCapScalingStatement.{u}) (geometry : NeckLossGeometryProducerStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  public_after_ten triangulate atlas (ricci_producer_of_neck_loss allowances scaling geometry)
#print axioms NeckControlledHistory.toRicci
#print axioms anchored_neck_to_ricci
#print axioms ricci_producer_of_neck_loss
#print axioms public_of_neck_loss_frontier
end PoincareConjecture.ProofContract.Refinement20260927
