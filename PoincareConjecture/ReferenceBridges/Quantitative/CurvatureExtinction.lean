import Mathlib
import PoincareConjecture.ParallelMath.Core
import ReferenceBridges.Quantitative.CoefficientDomination
import ReferenceBridges.ParallelMath.FiniteExtinctionObstruction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative.Reference
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff

/-- **Math.** A lower coefficient bound suffices for the finite-jump scalar extinction obstruction. -/
theorem finite_horizon_under_coefficient_bound (alpha c a k : ℝ)
    (hc : 0 < c) (hk : 0 < k) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ T : ℝ, 0 < T ∧
      ∀ (n : ℕ) (time : ℕ → ℝ) (u : ℕ → ℝ → ℝ) (q : ℝ → ℝ),
        0 < n → StrictMono time → time 0 = 0 → T ≤ time n →
        (∀ i < n, ContinuousOn (u i) (Icc (time i) (time (i+1)))) →
        (∀ i < n, ∀ t ∈ Ico (time i) (time (i+1)),
          MorganTianLib.ForwardDiffQuotientLE (u i) t (-k-q t*u i t)) →
        (∀ t ∈ Icc 0 (time n), -(alpha/(t+c)) ≤ q t) →
        (∀ i < n, ∀ t ∈ Icc (time i) (time (i+1)), 0 ≤ u i t) →
        u 0 0 ≤ a →
        (∀ i, i+1 < n → u (i+1) (time (i+1)) ≤ u i (time (i+1))) → False :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨T, hTpos, hT⟩ :=
    _root_.PoincareConjecture.ParallelMath.Reference.finite_horizon_for_nonnegative_width
      alpha c a k hc hk ha0 ha1
  refine ⟨T, hTpos, ?_⟩
  intro n time u q hn htime htime0 hTle hu hdu hq hunneg hinit hjumps
  have hmono : Monotone time := htime.monotone
  refine hT n time u hn htime htime0 hTle hu ?_ hunneg hinit hjumps
  intro i hi t ht
  have htIcc : t ∈ Icc (time i) (time (i + 1)) := Ico_subset_Icc_self ht
  have ht0n : t ∈ Icc 0 (time n) := by
    have hsub : Icc (time i) (time (i + 1)) ⊆ Icc (time 0) (time n) :=
      Icc_subset_Icc (hmono (Nat.zero_le i)) (hmono (Nat.succ_le_of_lt hi))
    simpa [htime0] using hsub htIcc
  exact forwardDiff_of_coefficient_lower_bound (u i) q alpha c k t
    (hunneg i hi t htIcc) (hq t ht0n) (hdu i hi t ht)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
