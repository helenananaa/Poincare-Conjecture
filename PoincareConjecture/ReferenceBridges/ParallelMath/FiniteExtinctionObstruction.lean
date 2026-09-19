import PoincareConjecture.ParallelMath.Extinction.PowerDerivative
import PoincareConjecture.ParallelMath.Extinction.PowerNegative
import ReferenceBridges.ParallelMath.FiniteDini
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Reference
open Set Function Filter
open scoped Topology BigOperators
/-- Scalar finite extinction with an arbitrary finite number of downward jumps.
No geometric width evolution or surgery finiteness is asserted by this lemma. -/
theorem finite_horizon_for_nonnegative_width (alpha c a k : ℝ)
    (hc : 0 < c) (hk : 0 < k) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ T : ℝ, 0 < T ∧
      ∀ (n : ℕ) (time : ℕ → ℝ) (u : ℕ → ℝ → ℝ),
        0 < n → StrictMono time → time 0 = 0 → T ≤ time n →
        (∀ i < n, ContinuousOn (u i) (Icc (time i) (time (i+1)))) →
        (∀ i < n, ∀ t ∈ Ico (time i) (time (i+1)),
          MorganTianLib.ForwardDiffQuotientLE (u i) t
            (-k + alpha/(t+c)*u i t)) →
        (∀ i < n, ∀ t ∈ Icc (time i) (time (i+1)), 0 ≤ u i t) →
        u 0 0 ≤ a →
        (∀ i, i+1 < n → u (i+1) (time (i+1)) ≤ u i (time (i+1))) → False :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨T0, hT0_nonneg, hT0⟩ :=
    powerBarrier_eventually_negative alpha c a k hc hk ha0 ha1
  refine ⟨T0 + 1, add_pos_of_nonneg_of_pos hT0_nonneg one_pos, ?_⟩
  intro n time u hn htime htime0 hTle hu hdu hunneg hinit hjumps
  set G : ℝ → ℝ := powerBarrier alpha c a k
  set psi : ℝ → ℝ → ℝ := fun t y => -k + alpha / (t + c) * y
  have hα1 : alpha ≠ 1 := ha1.ne
  have time_nonneg : ∀ i, 0 ≤ time i := fun i => by
    simpa [htime0] using htime.monotone (Nat.zero_le i)
  have tc_pos : ∀ t : ℝ, 0 ≤ t → 0 < t + c := fun t ht =>
    add_pos_of_nonneg_of_pos ht hc
  have hG0 : G 0 = a := by
    have hcα : (c : ℝ) ^ alpha ≠ 0 := (Real.rpow_pos_of_pos hc alpha).ne'
    calc
      G 0 = (0 + c) ^ alpha *
          (a / c ^ alpha - k / (1 - alpha) *
            ((0 + c) ^ (1 - alpha) - c ^ (1 - alpha))) := rfl
      _ = c ^ alpha *
          (a / c ^ alpha - k / (1 - alpha) *
            (c ^ (1 - alpha) - c ^ (1 - alpha))) := by
        simp only [zero_add]
      _ = c ^ alpha * (a / c ^ alpha - k / (1 - alpha) * 0) := by
        simp only [sub_self]
      _ = c ^ alpha * (a / c ^ alpha) := by
        simp only [mul_zero, sub_zero]
      _ = a := mul_div_cancel₀ a hcα
  have hpsi : ContDiffOn ℝ 1 (uncurry psi)
      (Icc (time 0) (time n) ×ˢ (univ : Set ℝ)) := by
    have hden : ∀ p : ℝ × ℝ,
        p ∈ Icc (time 0) (time n) ×ˢ (univ : Set ℝ) → p.1 + c ≠ 0 := by
      intro p hp
      have ht0 : 0 ≤ p.1 := (time_nonneg 0).trans hp.1.1
      exact (tc_pos p.1 ht0).ne'
    rw [uncurry_def]
    exact contDiffOn_const.add
      (((contDiffOn_const (c := alpha)).div
          (contDiffOn_fst.add contDiffOn_const) hden).mul
        contDiffOn_snd)
  have hG : ContinuousOn G (Icc (time 0) (time n)) := by
    refine HasDerivAt.continuousOn (f' := fun t => psi t (G t)) ?_
    intro t ht
    have ht0 : 0 ≤ t := (time_nonneg 0).trans ht.1
    exact powerBarrier_hasDerivAt alpha c a k t (tc_pos t ht0) hα1
  have hdG : ∀ t ∈ Ico (time 0) (time n),
      HasDerivWithinAt G (psi t (G t)) (Ici t) t := by
    intro t ht
    have ht0 : 0 ≤ t := (time_nonneg 0).trans ht.1
    exact (powerBarrier_hasDerivAt alpha c a k t (tc_pos t ht0) hα1).hasDerivWithinAt
  have hinit' : u 0 (time 0) ≤ G (time 0) := by
    simpa [htime0, hG0] using hinit
  have hcmp :=
    finite_forward_comparison n time htime u G psi hu hdu hpsi hG hdG hinit' hjumps
  have hi : n - 1 < n := Nat.sub_lt hn Nat.one_pos
  have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have htmem : time n ∈ Icc (time (n - 1)) (time (n - 1 + 1)) := by
    rw [hsucc]
    exact ⟨htime.monotone (Nat.sub_le n 1), le_rfl⟩
  have hle : u (n - 1) (time n) ≤ G (time n) := hcmp (n - 1) hi (time n) htmem
  have hnn : 0 ≤ u (n - 1) (time n) := hunneg (n - 1) hi (time n) htmem
  have hGneg : G (time n) < 0 :=
    hT0 (time n) ((le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)).trans hTle)
  exact (not_lt_of_ge (hnn.trans hle)) hGneg
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Reference
