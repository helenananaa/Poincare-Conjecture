import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.ZeroTraceValueSmallness
import PoincareConjecture.ParallelImplementation.GradientSupInterpolation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ZeroTraceLowerJetSmallness
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open scoped Topology ContDiff BoundedContinuousFunction
/-- Quantitative small-time control of the value and gradient of a genuine zero-initial-value jet. -/
theorem zero_trace_lower_jet_smallness (T alpha : ℝ) (hT : 0 < T)
    (z : FullJet T) (hz : z ∈ fullParabolicJetSet T alpha hT.le) :
    ‖z.1.1.1.1‖ ≤ T*‖z.1.2‖ ∧
      ‖z.1.1.1.2.1‖ ≤
        (2*‖z.1.2‖ + ‖z.1.1.1.2.2‖)*Real.sqrt T :=
/- SWARM_PROOF_BEGIN -/
by
  have hsmall :=
    PoincareConjecture.ParallelImplementation.ZeroTraceValueSmallness.zero_trace_value_smallness
      T alpha hT.le z hz
  refine ⟨hsmall.2, ?_⟩
  let f (t : Set.Icc (0 : ℝ) T) :
      EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 6) :=
    fun x => z.1.1.1.1 (t,x)
  let A : ℝ := T * ‖z.1.2‖
  let M : ℝ := ‖z.1.1.1.2.2‖
  let r : ℝ := Real.sqrt T
  have hjet : z.1.1.1 ∈ spaceTimeC2JetSet T := hz.1.1
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hM : 0 ≤ M := by
    exact norm_nonneg _
  have hr : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hT
  have hpoint : ∀ t : Set.Icc (0 : ℝ) T, ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖z.1.1.1.2.1 (t,x)‖ ≤ 2*A/r + M*r := by
    intro t x
    have hC2 : ContDiff ℝ 2 (f t) :=
      (spaceTime_C2_jet_complete T).2 z.1.1.1 hjet t
    have hvalue : ∀ y : EuclideanSpace ℝ (Fin 3), ‖f t y‖ ≤ A := by
      intro y
      dsimp [f, A]
      calc
        ‖z.1.1.1.1 (t,y)‖ ≤ (t : ℝ) * ‖z.1.2‖ := hsmall.1 t y
        _ ≤ T * ‖z.1.2‖ :=
          mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg _)
    have hslice := hjet t
    have hgradFun : (fun y : EuclideanSpace ℝ (Fin 3) => fderiv ℝ (f t) y) =
        (fun y => z.1.1.1.2.1 (t,y)) := by
      funext y
      exact (hslice.1 y).fderiv
    have hhess : ∀ y : EuclideanSpace ℝ (Fin 3),
        ‖fderiv ℝ (fderiv ℝ (f t)) y‖ ≤ M := by
      intro y
      have hsecondEq : fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
          fderiv ℝ (f t) w) y = z.1.1.1.2.2 (t,y) := by
        calc
          _ = fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
              z.1.1.1.2.1 (t,w)) y := by rw [hgradFun]
          _ = z.1.1.1.2.2 (t,y) := (hslice.2 y).fderiv
      rw [hsecondEq]
      exact BoundedContinuousFunction.norm_coe_le_norm z.1.1.1.2.2 (t,y)
    have hgrad :=
      PoincareConjecture.ParallelImplementation.GradientSupInterpolation.gradient_sup_interpolation
        (f t) hC2 A M r hA hM hr hvalue hhess
    have hxEq : z.1.1.1.2.1 (t,x) = fderiv ℝ (f t) x :=
      (congrFun hgradFun x).symm
    simpa [hxEq] using hgrad x
  have hboundNonneg : 0 ≤ (2*A/r + M*r) := by positivity
  have hnorm : ‖z.1.1.1.2.1‖ ≤ 2*A/r + M*r := by
    apply (BoundedContinuousFunction.norm_le hboundNonneg).2
    intro p
    rcases p with ⟨s,x⟩
    exact hpoint s x
  have hrewrite : 2*A/r + M*r =
      (2*‖z.1.2‖ + ‖z.1.1.1.2.2‖) * Real.sqrt T := by
    dsimp [A, M, r]
    have hsquare : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
    field_simp [ne_of_gt (Real.sqrt_pos.2 hT)]
    nlinarith
  rw [hrewrite] at hnorm
  exact hnorm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ZeroTraceLowerJetSmallness
