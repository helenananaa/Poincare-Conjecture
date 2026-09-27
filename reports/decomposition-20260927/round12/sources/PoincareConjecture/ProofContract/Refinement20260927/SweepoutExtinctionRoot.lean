import PoincareConjecture.ProofContract.Refinement20260927.MinimaxComparison
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
/-- **Math.** A survival certificate built from inf-sup spectra and transfers,
not free scalar width values. Geometric energy/homotopy realization remains
an explicit research gap; these data do NOT claim to construct minimal spheres. -/
structure MinimaxSurvivalProfile (a c w0 T : ℝ) (events : Set ℝ) where
  before : ℝ → SweepoutSpectrum.{u}
  after : ℝ → SweepoutSpectrum.{u}
  initial : (after 0).width 0 ≤ w0
  transfer : ∀ t ∈ events, SweepoutTransfer (before t) (after t) t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ F : SweepoutSpectrum.{u}, ContinuousOn F.width (Icc s t) ∧
      F.width s = (after s).width s ∧ F.width t = (before t).width t ∧
      ∀ r ∈ Ico s t, Nonempty (GoodSweepoutAt F r a (3/(4*(r+c))))
/-- **Math.** Nonnegativity and jumps now follow from the specified spectra;
Dini estimates follow from uniform near-max comparison and sequence limits. -/
def MinimaxSurvivalProfile.toExtinction (nearMax : UniformNearMaxTaylorStatement)
    (limitPass : MinimaxDiniLimitStatement) {a c w0 T : ℝ} {E : Set ℝ}
    (ha : 0 < a) (hc : 0 < c) (W : MinimaxSurvivalProfile.{u} a c w0 T E) :
    ExtinctionProfile a c w0 T E where
  pre := fun t => (W.before t).width t
  post := fun t => (W.after t).width t
  initial := W.initial
  terminal_nonneg := (W.before T).width_nonneg T
  jumps := fun t ht => (W.transfer t ht).width_le
  intervals := by
    intro s t hs hst ht hgap
    obtain ⟨F,hcont,hstart,hend,hgood⟩ := W.intervals s t hs hst ht hgap
    refine ⟨F.width,hcont,hstart,hend,?_⟩
    intro r hr
    obtain ⟨G⟩ := hgood r hr
    have hrc : 0 < r+c := by linarith [hr.1]
    exact width_dini_of_good_sweepouts nearMax limitPass F r a (3/(4*(r+c))) ha
      (div_nonneg (by norm_num) (mul_nonneg (by norm_num) hrc.le)) G
/-- **Math.** RESEARCH: spectra must come from a controlled geometric flow,
with good-sweepout production, energy/homotopy interpretation and transfers.
No claimed existence theorem is hidden in this declaration. -/
def MinimaxControlledGeometryProducerStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) [IsSmooth M] (d : MetricInitialData M),
    SimplyConnectedSpace M → ∃ B a c w0 : ℝ,
      0 ≤ B ∧ 0 < a ∧ 0 < c ∧ 0 ≤ w0 ∧
      ∀ eps : ℝ, 0 < eps → ∀ T : ℝ, 0 < T →
        ∃ H : LocatedProjection checked_epsilon_neck_embedding.{u} M,
          H.horizon = T ∧ PatchNeckBudget checked_epsilon_neck_embedding.{u} M d B eps H ∧
          (H.pre H.horizon ≠ [] → Nonempty (MinimaxSurvivalProfile.{u} a c w0 H.horizon H.events))
theorem width_producer_of_minimax (nearMax : UniformNearMaxTaylorStatement)
    (limitPass : MinimaxDiniLimitStatement)
    (produce : MinimaxControlledGeometryProducerStatement.{u}) :
    WidthControlledGeometryProducerStatement.{u} := by
  intro M hsm d hsc
  obtain ⟨B,a,c,w0,hB,ha,hc,hw,run⟩ := produce M d hsc
  refine ⟨B,a,c,w0,hB,ha,hc,hw,?_⟩
  intro eps heps T hT
  obtain ⟨H,hH,budget,profile⟩ := run eps heps T hT
  refine ⟨H,hH,budget,?_⟩
  intro hsurvive
  obtain ⟨W⟩ := profile hsurvive
  exact ⟨W.toExtinction nearMax limitPass ha hc⟩
/-- **Math.** Checked reduction from the two scalar leaves and three remaining
research obligations to the exact original public target. -/
theorem public_of_sweepout_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (nearMax : UniformNearMaxTaylorStatement)
    (limitPass : MinimaxDiniLimitStatement)
    (geometry : MinimaxControlledGeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_after_seventeen triangulate atlas (width_producer_of_minimax nearMax limitPass geometry)
#print axioms MinimaxSurvivalProfile.toExtinction
#print axioms width_producer_of_minimax
#print axioms public_of_sweepout_frontier
end PoincareConjecture.ProofContract.Refinement20260927
