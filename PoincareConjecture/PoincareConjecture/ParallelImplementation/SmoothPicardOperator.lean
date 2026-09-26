import PoincareConjecture.ParallelImplementation.SmoothPathSuperposition
import DoCarmoLib.Riemannian.Geodesic.FlowDependence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothPicardOperator
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
def timeState {T : ℝ} (u : C(Set.Icc (0 : ℝ) T, E)) :
    C(Set.Icc (0 : ℝ) T, ℝ × E) :=
  ⟨fun t => ((t : ℝ), u t), continuous_subtype_val.prodMk u.continuous⟩
def picardOperator {T : ℝ} (hT : 0 ≤ T)
    (f : ℝ × E → E) (hf : Continuous f) :
    E × C(Set.Icc (0 : ℝ) T, E) → C(Set.Icc (0 : ℝ) T, E) :=
  fun q => ContinuousMap.const _ q.1 +
    Riemannian.FlowDependence.intervalPrimitive hT
      ⟨fun t => f (timeState q.2 t), hf.comp (timeState q.2).continuous⟩
/-- Joint initial-value/path smoothness of the actual time-dependent Picard integral operator. -/
theorem contDiff_picardOperator {T : ℝ} (hT : 0 ≤ T)
    (f : ℝ × E → E) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (picardOperator hT f hf.continuous) :=
/- SWARM_PROOF_BEGIN -/
by
  let S := Set.Icc (0 : ℝ) T
  let c : C(S, ℝ × E) :=
    ⟨fun t => ((t : ℝ), 0), continuous_subtype_val.prodMk continuous_const⟩
  let incl : C(S, E) →L[ℝ] C(S, ℝ × E) :=
    ContinuousLinearMap.compLeftContinuous ℝ S (ContinuousLinearMap.inr ℝ ℝ E)
  have htimeState : ContDiff ℝ ∞ (timeState (T := T) : C(S, E) → C(S, ℝ × E)) := by
    have heq : (timeState (T := T) : C(S, E) → C(S, ℝ × E)) =
        fun u => c + incl u := by
      funext u
      ext t
      · simp [timeState, c, incl, ContinuousLinearMap.compLeftContinuous]
      · simp [timeState, c, incl, ContinuousLinearMap.compLeftContinuous]
    rw [heq]
    exact contDiff_const.add incl.contDiff
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_Icc)
  let super : C(S, ℝ × E) → C(S, E) :=
    PoincareConjecture.ParallelImplementation.SmoothPathSuperposition.superposition
      f hf.continuous
  have hsuper : ContDiff ℝ ∞ super := by
    exact PoincareConjecture.ParallelImplementation.SmoothPathSuperposition.contDiff_superposition
      f hf
  let init : E →L[ℝ] C(S, E) := ContinuousLinearMap.const ℝ S
  let hpath : E × C(S, E) → C(S, E) :=
    fun q => init q.1 + Riemannian.FlowDependence.intervalPrimitive hT
      (super (timeState q.2))
  have hpath_smooth : ContDiff ℝ ∞ hpath := by
    have htime : ContDiff ℝ ∞ (fun q : E × C(S, E) => timeState q.2) := by
      have hsnd : ContDiff ℝ ∞ (fun q : E × C(S, E) => q.2) :=
        (ContinuousLinearMap.snd ℝ E (C(S, E))).contDiff
      exact htimeState.comp hsnd
    have hinit : ContDiff ℝ ∞ (fun q : E × C(S, E) => init q.1) := by
      have hfst : ContDiff ℝ ∞ (fun q : E × C(S, E) => q.1) :=
        (ContinuousLinearMap.fst ℝ E (C(S, E))).contDiff
      exact init.contDiff.comp hfst
    have hint : ContDiff ℝ ∞
        (fun q : E × C(S, E) =>
          Riemannian.FlowDependence.intervalPrimitive hT (super (timeState q.2))) := by
      exact (Riemannian.FlowDependence.intervalPrimitive hT).contDiff.comp
        (hsuper.comp htime)
    exact hinit.add hint
  have heq : (picardOperator hT f hf.continuous : E × C(S, E) → C(S, E)) = hpath := by
    funext q
    rfl
  rw [heq]
  exact hpath_smooth
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothPicardOperator
