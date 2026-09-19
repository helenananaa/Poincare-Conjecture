import Mathlib
import PoincareConjecture.ParallelMath.Core
import MorganTianLib.Ch02.EpsilonClose
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative.Reference
open Set Function Filter Riemannian
open scoped BigOperators Topology Manifold ContDiff
open MorganTianLib
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Express an arbitrary second metric bilinear form using the first metric frame. -/
theorem metric_bilinear_frame_expansion (g0 g : Riemannian.RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    g.metricInner p v w =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        g.metricInner p (orthoFrameField g0 p i p) (orthoFrameField g0 p j p) *
          g0.metricInner p v (orthoFrameField g0 p i p) * g0.metricInner p w (orthoFrameField g0 p j p) :=
/- SWARM_PROOF_BEGIN -/
by
  have hp : p ∈ orthoFrameSet (I := I) (M := M) p :=
    mem_orthoFrameSet_self (I := I) (M := M) p
  have hv : v =
      ∑ i, g0.metricInner p v (orthoFrameField g0 p i p) •
        orthoFrameField g0 p i p :=
    orthoFrameField_expansion (I := I) g0 p hp v
  have hw : w =
      ∑ j, g0.metricInner p w (orthoFrameField g0 p j p) •
        orthoFrameField g0 p j p :=
    orthoFrameField_expansion (I := I) g0 p hp w
  have hsum_left :
      ∀ (s : Finset (Fin (Module.finrank ℝ E)))
        (c : Fin (Module.finrank ℝ E) → ℝ)
        (vs : Fin (Module.finrank ℝ E) → TangentSpace I p)
        (z : TangentSpace I p),
      g.metricInner p (∑ a ∈ s, c a • vs a) z =
        ∑ a ∈ s, c a * g.metricInner p (vs a) z := by
    intro s c vs z
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, g.metricInner_add_left, g.metricInner_smul_left, ih,
        Finset.sum_insert ha]
  have hsum_right :
      ∀ (s : Finset (Fin (Module.finrank ℝ E)))
        (c : Fin (Module.finrank ℝ E) → ℝ)
        (z : TangentSpace I p)
        (ws : Fin (Module.finrank ℝ E) → TangentSpace I p),
      g.metricInner p z (∑ a ∈ s, c a • ws a) =
        ∑ a ∈ s, c a * g.metricInner p z (ws a) := by
    intro s c z ws
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, g.metricInner_add_right, g.metricInner_smul_right, ih,
        Finset.sum_insert ha]
  conv_lhs => rw [hv, hw]
  rw [hsum_left Finset.univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsum_right Finset.univ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
