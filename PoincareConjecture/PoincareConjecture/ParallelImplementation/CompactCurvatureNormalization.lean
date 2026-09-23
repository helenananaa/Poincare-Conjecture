import PoincareConjecture.ParallelImplementation.CompactCurvatureOperatorBound
import MorganTianLib.Ch01.MetricRescaling
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.CompactCurvatureNormalization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
theorem exists_rescaling_curvature_bound_one (g : RiemannianMetric I M) :
    ∃ c : ℝ, ∃ hc : 0 < c, ∀ q : M,
      MorganTianLib.HasCurvatureOperatorNormLeAt (MorganTianLib.rescaledMetric g c hc)
        (MorganTianLib.rescaledMetric g c hc).leviCivitaConnection
        ((MorganTianLib.rescaledMetric g c hc).leviCivitaConnection.isLeviCivita_of_koszulDual
          (MorganTianLib.rescaledMetric g c hc)
          (fun X Y Z p => (MorganTianLib.rescaledMetric g c hc).koszulDualSection_dual X Y Z p)) q 1 :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hC, hcomponents⟩ :=
    _root_.PoincareConjecture.ParallelImplementation.CompactCurvatureBound.exists_compact_uniform_curvature_frame_component_bound g
  have hd : 0 < Module.finrank ℝ E :=
    Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hdR : 0 < (Module.finrank ℝ E : ℝ) := by exact_mod_cast hd
  let c : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * (C + 1)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (sq_pos_of_pos hdR) (by linarith)
  let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y Z p => g.koszulDualSection_dual X Y Z p)
  refine ⟨c, hc, ?_⟩
  intro q
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨a, hqa, hbound⟩ := hcomponents q
  let b := MorganTianLib.orthoFrameBasis g a hqa
  let B := MorganTianLib.curvatureFormAt g g.leviCivitaConnection q
  have hcomp : ∀ i j k l : Fin (Module.finrank ℝ E),
      |B (b i) (b j) (b k) (b l)| ≤ C + 1 := by
    intro i j k l
    simpa [B, b, MorganTianLib.orthoFrameBasis_apply] using
      (le_trans (hbound i j k l) (by linarith : C ≤ C + 1))
  have halg : Riemannian.IsAlgCurvatureForm B :=
    MorganTianLib.isAlgCurvatureForm_curvatureFormAt g
      g.leviCivitaConnection hLC q
  have hop :=
    _root_.PoincareConjecture.ParallelImplementation.ExteriorCurvatureBound.curvatureOperator_bound_of_components
        (d := Module.finrank ℝ E) b halg (C + 1) (by linarith) hcomp
  have hbase :
      MorganTianLib.HasCurvatureOperatorNormLeAt g g.leviCivitaConnection
        hLC q c := by
    simpa [MorganTianLib.HasCurvatureOperatorNormLeAt, hLC, c] using hop
  let g' := MorganTianLib.rescaledMetric g c hc
  let hLC' := g'.leviCivitaConnection.isLeviCivita_of_koszulDual g'
    (fun X Y Z p => g'.koszulDualSection_dual X Y Z p)
  have hscale :=
    MorganTianLib.rescaledMetric_hasCurvatureOperatorNormLeAt_div_iff
      g c hc hLC hLC' q c
  simpa [g', hLC', div_self (ne_of_gt hc)] using hscale.mpr hbase
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CompactCurvatureNormalization
