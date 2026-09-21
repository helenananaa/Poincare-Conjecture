import MorganTianLib.Ch02.SurgeryCap.RoundTipWarping

open Set
open scoped ContDiff
noncomputable section
namespace MorganTianLib.SurgeryCap

/-- **Math.** Scalar profile of a rotationally symmetric cap. Its geometric
realization, curvature and completeness are separate results. -/
structure RoundCapProfile where
  r0 : ℝ
  A : ℝ
  w : ℝ → ℝ
  r0_pos : 0 < r0
  r0_lt_A : r0 < A
  smooth : ContDiff ℝ ∞ w
  tip : ∀ r, |r| ≤ r0 → w r = 2 * Real.sin (r / 2)
  tail : ∀ r, A ≤ r → w r = Real.sqrt 2
  positive : ∀ r, 0 < r → 0 < w r
  deriv_bounds : ∀ r, 0 ≤ r → deriv w r ∈ Icc (0 : ℝ) 1
  deriv_strict : ∀ r, 0 < r → deriv w r < 1
  concave : ∀ r, 0 ≤ r → deriv (deriv w) r ≤ 0

/-- **Math.** The profile data is genuinely inhabited, using the checked
round-tip and cylindrical-tail construction, not an assumed profile. -/
theorem nonempty_roundCapProfile : Nonempty RoundCapProfile := by
  obtain ⟨r0, A, w, h0, hA, hs, ht, he, hp, hd, hl, hc⟩ :=
    exists_round_tip_cylindrical_warping
  exact ⟨⟨r0, A, w, h0, hA, hs, ht, he, hp, hd, hl, hc⟩⟩

/-- **Math.** Fix one of the constructed profiles once and for all. -/
def standardRoundCapProfile : RoundCapProfile :=
  Classical.choice nonempty_roundCapProfile

@[simp] theorem RoundCapProfile.w_zero (P : RoundCapProfile) : P.w 0 = 0 := by
  simpa using P.tip 0 (by simpa using P.r0_pos.le)

/-- **Math.** The candidate tangential sectional-curvature coefficient.
Identification with geometric curvature must be proved for the actual metric. -/
def RoundCapProfile.tangentialCoefficient (P : RoundCapProfile) (r : ℝ) : ℝ :=
  (1 - deriv P.w r ^ 2) / P.w r ^ 2

/-- **Math.** The candidate radial sectional-curvature coefficient. -/
def RoundCapProfile.radialCoefficient (P : RoundCapProfile) (r : ℝ) : ℝ :=
  -deriv (deriv P.w) r / P.w r

end MorganTianLib.SurgeryCap
