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

/-- **Math.** The original metric closeness predicate is nonvacuous on any actual metric. -/
theorem epsilonClose_self (g0 : Riemannian.RiemannianMetric I M) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1/2) :
    MorganTianLib.EpsilonClose epsilon g0 g0 :=
/- SWARM_PROOF_BEGIN -/
by
  -- The covariant difference of a metric with itself vanishes at every order.
  have hiter :
      ∀ (n : ℕ) (X : Fin (n + 2) → SmoothVectorField I M) (q : M),
        iteratedCovariantMetricDifference g0 g0 n X q = 0 := by
    intro n
    induction n with
    | zero =>
      intro X q
      simp [iteratedCovariantMetricDifference]
    | succ n ih =>
      intro X q
      -- Unfold the successor: directional derivative of the previous
      -- tensor minus the Levi-Civita correction sum.
      rw [iteratedCovariantMetricDifference]
      -- The previous-order tensor is the zero function.
      have hfun :
          iteratedCovariantMetricDifference g0 g0 n (fun i => X i.succ) =
            fun _ => (0 : ℝ) :=
        funext fun r => ih (fun i => X i.succ) r
      -- Directional derivative of the zero function vanishes.
      have hdir :
          (X 0).dir (iteratedCovariantMetricDifference g0 g0 n
            (fun i => X i.succ)) q = 0 := by
        rw [hfun, SmoothVectorField.dir, mfderiv_const]
        rfl
      -- Each correction term vanishes by the inductive hypothesis.
      have hcorr :
          (∑ i : Fin (n + 2),
            iteratedCovariantMetricDifference g0 g0 n
              (Function.update (fun i => X i.succ) i
                (g0.leviCivitaConnection.cov (X 0)
                  ((fun i => X i.succ) i))) q) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i _
        exact ih _ _
      -- The two displayed lets in the definition reduce to `hdir - hcorr`.
      simp [hdir, hcorr]
  -- Pointwise squared-norm contractions therefore vanish.
  have hnorm : ∀ (n : ℕ) (q : M),
      metricCovariantDerivativeNormSq g0 g0 n q = 0 := by
    intro n q
    simp [metricCovariantDerivativeNormSq, hiter]
  -- The closeness density is a finite sum of those contractions.
  have hden : ∀ q : M, epsilonClosenessDensity epsilon g0 g0 q = 0 := by
    intro q
    simp [epsilonClosenessDensity, hnorm]
  -- Strict uniform witness `C = 0`, admissible because `0 < ε²`.
  refine ⟨he0, he1, (0 : ℝ), ?_, ?_⟩
  · exact pow_pos he0 2
  · intro p
    simp [hden p]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
