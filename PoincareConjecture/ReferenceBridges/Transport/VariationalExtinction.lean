import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import PoincareConjecture.ParallelMath.Transport.WidthLocalContinuity
import ReferenceBridges.Transport.DiniInfApproximate
import ReferenceBridges.ParallelMath.FiniteExtinctionObstruction
import PoincareConjecture.ParallelMath.Variational.AdmissibleTransfer

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport.Reference
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** A nonattained variational infimum has a finite time horizon from approximate-competitor estimates and explicit admissible jump maps. -/
theorem finite_horizon_from_approximate_width_competitors {A : Type*} [Nonempty A]
    (alpha c a k : ℝ) (hc : 0 < c) (hk : 0 < k) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ T : ℝ, 0 < T ∧ ∀ (n : ℕ) (time : ℕ → ℝ) (F : ℕ → ℝ → A → ℝ) (K : ℕ → ℝ),
      0 < n → StrictMono time → time 0 = 0 → T ≤ time n →
      (∀ i t x, 0 ≤ F i t x) →
      (∀ i < n, 0 ≤ K i) →
      (∀ i < n, ∀ s ∈ Icc (time i) (time (i+1)),
        ∀ t ∈ Icc (time i) (time (i+1)), ∀ x,
          F i t x ≤ Real.exp (K i*|t-s|)*F i s x) →
      (∀ i < n, ∀ s ∈ Ico (time i) (time (i+1)), ∀ eta : ℝ, 0 < eta →
        ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ, 0 < h → h < delta → ∃ x : A,
          F i s x ≤ PoincareConjecture.ParallelMath.Variational.leastCost (F i s)+eta*h ∧
          F i (s+h) x ≤ F i s x+((-k+alpha/(s+c)*PoincareConjecture.ParallelMath.Variational.leastCost (F i s))+eta)*h) →
      PoincareConjecture.ParallelMath.Variational.leastCost (F 0 0) ≤ a →
      (∀ i, i+1 < n → ∃ tr : A → A,
        ∀ x, F (i+1) (time (i+1)) (tr x) ≤ F i (time (i+1)) x) → False :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨T, hTpos, hT⟩ :=
    _root_.PoincareConjecture.ParallelMath.Reference.finite_horizon_for_nonnegative_width
      alpha c a k hc hk ha0 ha1
  refine ⟨T, hTpos, ?_⟩
  intro n time F K hn htime htime0 hTle hFnonneg hK hdist happrox hinit hjumps
  set u : ℕ → ℝ → ℝ :=
    fun i t => PoincareConjecture.ParallelMath.Variational.leastCost (F i t)
  refine hT n time u hn htime htime0 hTle ?hu ?hdu ?hunneg hinit ?hjumpsU
  · intro i hi
    exact
      _root_.PoincareConjecture.ParallelMath.Transport.leastCost_continuousOn_of_exp_distortion
        (F i) (Icc (time i) (time (i + 1))) (K i) (hK i hi)
        (fun t _ x => hFnonneg i t x) (hdist i hi)
  · intro i hi t ht
    exact leastCost_forwardDiff_of_approximate_competitors (F i) t
      (-k + alpha / (t + c) * u i t)
      (fun s x => hFnonneg i s x) (happrox i hi t ht)
  · intro i hi t _ht
    exact
      (PoincareConjecture.ParallelMath.Variational.leastCost_nonneg_and_approx
        (F i t) (fun x => hFnonneg i t x)).1
  · intro i hi
    obtain ⟨tr, htr⟩ := hjumps i hi
    have htr' :=
      PoincareConjecture.ParallelMath.Variational.leastCost_transfer
        (F i (time (i + 1))) (F (i + 1) (time (i + 1)))
        (fun x => hFnonneg i (time (i + 1)) x)
        (fun x => hFnonneg (i + 1) (time (i + 1)) x)
        tr 1 0 (zero_le_one : (0 : ℝ) ≤ 1)
        (fun x => by simpa using htr x)
    simpa using htr'
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport.Reference
