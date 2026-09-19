import MorganTianLib.Ch02.ForwardDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Reference
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff Bundle RealInnerProductSpace

/-- Scalar forward comparison persists through a finite sequence of downward jumps. -/
theorem finite_forward_comparison
    (n : ℕ) (time : ℕ → ℝ) (htime : StrictMono time)
    (u : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (psi : ℝ → ℝ → ℝ)
    (hu : ∀ i < n, ContinuousOn (u i) (Icc (time i) (time (i+1))))
    (hdu : ∀ i < n, ∀ t ∈ Ico (time i) (time (i+1)),
      MorganTianLib.ForwardDiffQuotientLE (u i) t (psi t (u i t)))
    (hpsi : ContDiffOn ℝ 1 (uncurry psi) (Icc (time 0) (time n) ×ˢ (univ : Set ℝ)))
    (hG : ContinuousOn G (Icc (time 0) (time n)))
    (hdG : ∀ t ∈ Ico (time 0) (time n), HasDerivWithinAt G (psi t (G t)) (Ici t) t)
    (hinit : u 0 (time 0) ≤ G (time 0))
    (hjumps : ∀ i, i+1 < n → u (i+1) (time (i+1)) ≤ u i (time (i+1))) :
    ∀ i < n, ∀ t ∈ Icc (time i) (time (i+1)), u i t ≤ G t :=
/- SWARM_PROOF_BEGIN -/
by
  have hmono : Monotone time := htime.monotone
  have hIcc : ∀ i, i < n → Icc (time i) (time (i + 1)) ⊆ Icc (time 0) (time n) :=
    fun i hi => Icc_subset_Icc (hmono (Nat.zero_le i)) (hmono (Nat.succ_le_of_lt hi))
  have hIco : ∀ i, i < n → Ico (time i) (time (i + 1)) ⊆ Ico (time 0) (time n) :=
    fun i hi => Ico_subset_Ico (hmono (Nat.zero_le i)) (hmono (Nat.succ_le_of_lt hi))
  -- On each interval, the scalar comparison lemma applies once the left endpoint
  -- is dominated by `G`. Coefficient and barrier hypotheses restrict by inclusion.
  have interval_le : ∀ i, i < n → u i (time i) ≤ G (time i) →
      ∀ t ∈ Icc (time i) (time (i + 1)), u i t ≤ G t := by
    intro i hi hstart
    refine MorganTianLib.le_of_forwardDiffQuotientLE (hu i hi) (hdu i hi)
      (hpsi.mono (prod_mono_left (hIcc i hi))) (hG.mono (hIcc i hi)) ?_ hstart
    intro s hs
    exact hdG s (hIco i hi hs)
  -- Initial values at later surgery times: previous terminal bound plus a downward jump.
  have start_le : ∀ i, i < n → u i (time i) ≤ G (time i) := by
    intro i
    induction i with
    | zero =>
      intro _hi
      exact hinit
    | succ i ih =>
      intro hi
      have hi0 : i < n := Nat.lt_of_succ_lt hi
      have hterm : u i (time (i + 1)) ≤ G (time (i + 1)) :=
        interval_le i hi0 (ih hi0) (time (i + 1)) ⟨hmono (Nat.le_succ i), le_rfl⟩
      exact (hjumps i hi).trans hterm
  intro i hi t ht
  exact interval_le i hi (start_le i hi) t ht
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Reference
