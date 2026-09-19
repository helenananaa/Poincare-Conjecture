import ReferenceBridges.Quantitative.RealLineLengthSpace
import ReferenceBridges.Quantitative.OpenCoverLipschitz
import Mathlib
import Shared.MetricGeometry.LengthSpace
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative.Reference
open Set Function Filter
open scoped BigOperators Topology
/-- **Math.** A uniform local Lipschitz constant on real neighborhoods is global. -/
theorem real_uniform_local_lipschitz_is_global {Y : Type*} [PseudoMetricSpace Y]
    (f : ℝ → Y) (L : NNReal)
    (hlocal : ∀ x : ℝ, ∃ r : ℝ, 0 < r ∧ LipschitzOnWith L f (Metric.ball x r)) :
    LipschitzWith L f :=
/- SWARM_PROOF_BEGIN -/
by
  -- Install only the already-proved length-space structure on ℝ.
  letI : Shared.LengthSpace ℝ := real_line_lengthSpace
  -- Choose a positive radius at each real center from the local Lipschitz data.
  choose r hr using hlocal
  -- Open balls of those radii form an open cover of ℝ.
  let U : ℝ → Set ℝ := fun x => Metric.ball x (r x)
  have hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
  have hcover : ∀ x, ∃ i, x ∈ U i := fun x => ⟨x, Metric.mem_ball_self (hr x).1⟩
  -- Glue the same map `f` on every ball of the cover.
  obtain ⟨F, hF, hFlip⟩ :=
    lipschitz_gluing_on_lengthSpace_open_cover U hU hcover (fun _ => f) L
      (fun _ _ _ _ _ => rfl) (fun i => (hr i).2)
  -- Coverage implies the glued map equals `f` pointwise.
  have hFf : F = f := by
    ext x
    obtain ⟨i, hxi⟩ := hcover x
    exact hF i x hxi
  -- Transfer the global Lipschitz bound from the glued map to `f`.
  rwa [hFf] at hFlip
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
