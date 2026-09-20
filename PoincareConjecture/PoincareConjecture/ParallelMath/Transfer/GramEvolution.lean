import PoincareConjecture.ParallelMath.Transfer.Core
import PoincareConjecture.ParallelMath.Variational.QuadraticDiscriminant
import PoincareConjecture.ParallelMath.Transport.PSDMixed

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath.Transfer
open Set

/-- If a time-dependent Gram form satisfies a relative variation bound, then
the Gram-area discriminant obeys `|Δ'| ≤ 2 K Δ`, and the area `A = √Δ`
obeys `|A'| ≤ K A` wherever `Δ > 0`. No Ricci flow. -/
theorem gram_det_variation_bound
    (E F G : ℝ → ℝ) (K t : ℝ) (hK : 0 ≤ K)
    (hE : HasDerivAt E (deriv E t) t)
    (hF : HasDerivAt F (deriv F t) t)
    (hG : HasDerivAt G (deriv G t) t)
    (hquad : ∀ s u : ℝ,
      |deriv E t * s ^ 2 + 2 * deriv F t * s * u + deriv G t * u ^ 2| ≤
        K * (E t * s ^ 2 + 2 * F t * s * u + G t * u ^ 2)) :
    let Δ := fun x => E x * G x - (F x) ^ 2
    |deriv Δ t| ≤ 2 * K * Δ t :=
/- SWARM_PROOF_BEGIN -/
by
  change |deriv (fun x => E x * G x - (F x) ^ 2) t| ≤
      2 * K * (E t * G t - (F t) ^ 2)
  set Δ : ℝ → ℝ := fun x => E x * G x - (F x) ^ 2
  have hF2 : HasDerivAt (fun x => (F x) ^ 2) (2 * F t * deriv F t) t := by
    have h := (hasDerivAt_pow 2 (F t)).comp t hF
    exact h.congr_deriv (by simp [pow_one])
  have hEG : HasDerivAt (fun x => E x * G x)
      (deriv E t * G t + E t * deriv G t) t :=
    hE.fun_mul hG
  have hΔ : HasDerivAt Δ
      (deriv E t * G t + E t * deriv G t - 2 * F t * deriv F t) t :=
    hEG.fun_sub hF2
  rw [hΔ.deriv]
  set Et := E t
  set Ft := F t
  set Gt := G t
  set Et' := deriv E t
  set Ft' := deriv F t
  set Gt' := deriv G t
  set Δt := Et * Gt - Ft ^ 2
  change |Et' * Gt + Et * Gt' - 2 * Ft * Ft'| ≤ 2 * K * Δt
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · -- K = 0 forces the variation form to vanish, hence Δ' = 0.
    have hK0' : K = 0 := hK0.symm
    have hform0 : ∀ s u : ℝ, Et' * s ^ 2 + 2 * Ft' * s * u + Gt' * u ^ 2 = 0 := by
      intro s u
      have h := hquad s u
      simp only [hK0', zero_mul] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hEt' : Et' = 0 := by simpa using hform0 1 0
    have hGt' : Gt' = 0 := by simpa using hform0 0 1
    have hFt' : Ft' = 0 := by
      have h := hform0 1 1
      simp only [hEt', hGt', one_pow, mul_one, add_zero, zero_add] at h
      linarith
    simp [hK0', hEt', hGt', hFt']
  · -- K > 0: |Q'| ≤ K Q implies Q, KQ-Q' and KQ+Q' are all PSD.
    have hQ : ∀ s u : ℝ, 0 ≤ Et * s ^ 2 + 2 * Ft * s * u + Gt * u ^ 2 := by
      intro s u
      have hKQ : 0 ≤ K * (Et * s ^ 2 + 2 * Ft * s * u + Gt * u ^ 2) :=
        (abs_nonneg _).trans (hquad s u)
      exact nonneg_of_mul_nonneg_right hKQ hKpos
    have hQdet :=
      PoincareConjecture.ParallelMath.Variational.quadratic_nonneg_det Et Ft Gt hQ
    have hP : ∀ s u : ℝ,
        0 ≤ (K * Et - Et') * s ^ 2 + 2 * (K * Ft - Ft') * s * u
          + (K * Gt - Gt') * u ^ 2 := by
      intro s u
      have hle := (abs_le.mp (hquad s u)).2
      have heq :
          (K * Et - Et') * s ^ 2 + 2 * (K * Ft - Ft') * s * u
              + (K * Gt - Gt') * u ^ 2
            = K * (Et * s ^ 2 + 2 * Ft * s * u + Gt * u ^ 2)
              - (Et' * s ^ 2 + 2 * Ft' * s * u + Gt' * u ^ 2) := by
        ring
      rw [heq]
      exact sub_nonneg.mpr hle
    have hN : ∀ s u : ℝ,
        0 ≤ (K * Et + Et') * s ^ 2 + 2 * (K * Ft + Ft') * s * u
          + (K * Gt + Gt') * u ^ 2 := by
      intro s u
      have hge := (abs_le.mp (hquad s u)).1
      have heq :
          (K * Et + Et') * s ^ 2 + 2 * (K * Ft + Ft') * s * u
              + (K * Gt + Gt') * u ^ 2
            = K * (Et * s ^ 2 + 2 * Ft * s * u + Gt * u ^ 2)
              + (Et' * s ^ 2 + 2 * Ft' * s * u + Gt' * u ^ 2) := by
        ring
      rw [heq]
      linarith
    have hPdet :=
      PoincareConjecture.ParallelMath.Variational.quadratic_nonneg_det
        (K * Et - Et') (K * Ft - Ft') (K * Gt - Gt') hP
    have hNdet :=
      PoincareConjecture.ParallelMath.Variational.quadratic_nonneg_det
        (K * Et + Et') (K * Ft + Ft') (K * Gt + Gt') hN
    -- Polarization: the mixed pairing of Q against KQ∓Q' is nonnegative.
    have hmixP :=
      PoincareConjecture.ParallelMath.Transport.psd2_mixed_determinant_nonneg
        Et Ft Gt (K * Et - Et') (K * Ft - Ft') (K * Gt - Gt')
        hQdet.1 hQdet.2.1 hPdet.1 hPdet.2.1 hQdet.2.2 hPdet.2.2
    have hmixN :=
      PoincareConjecture.ParallelMath.Transport.psd2_mixed_determinant_nonneg
        Et Ft Gt (K * Et + Et') (K * Ft + Ft') (K * Gt + Gt')
        hQdet.1 hQdet.2.1 hNdet.1 hNdet.2.1 hQdet.2.2 hNdet.2.2
    have hidP :
        Et * (K * Gt - Gt') + Gt * (K * Et - Et') - 2 * Ft * (K * Ft - Ft')
          = 2 * K * Δt - (Et' * Gt + Et * Gt' - 2 * Ft * Ft') := by
      ring
    have hidN :
        Et * (K * Gt + Gt') + Gt * (K * Et + Et') - 2 * Ft * (K * Ft + Ft')
          = 2 * K * Δt + (Et' * Gt + Et * Gt' - 2 * Ft * Ft') := by
      ring
    rw [abs_le]
    constructor
    · linarith
    · linarith
/- SWARM_PROOF_END -/

theorem gramArea_abs_deriv_le
    (E F G : ℝ → ℝ) (K t : ℝ) (hK : 0 ≤ K)
    (hE : HasDerivAt E (deriv E t) t)
    (hF : HasDerivAt F (deriv F t) t)
    (hG : HasDerivAt G (deriv G t) t)
    (hpos : 0 < E t * G t - (F t) ^ 2)
    (hquad : ∀ s u : ℝ,
      |deriv E t * s ^ 2 + 2 * deriv F t * s * u + deriv G t * u ^ 2| ≤
        K * (E t * s ^ 2 + 2 * F t * s * u + G t * u ^ 2)) :
    |deriv (fun x => Real.sqrt (E x * G x - (F x) ^ 2)) t| ≤
      K * Real.sqrt (E t * G t - (F t) ^ 2) :=
/- SWARM_PROOF_BEGIN -/
by
  set Δ : ℝ → ℝ := fun x => E x * G x - (F x) ^ 2
  have hF2 : HasDerivAt (fun x => (F x) ^ 2) (2 * F t * deriv F t) t := by
    have h := (hasDerivAt_pow 2 (F t)).comp t hF
    exact h.congr_deriv (by simp [pow_one])
  have hEG : HasDerivAt (fun x => E x * G x)
      (deriv E t * G t + E t * deriv G t) t :=
    hE.fun_mul hG
  have hΔ : HasDerivAt Δ
      (deriv E t * G t + E t * deriv G t - 2 * F t * deriv F t) t :=
    hEG.fun_sub hF2
  have hΔne : Δ t ≠ 0 := hpos.ne'
  have hsqrt : HasDerivAt (fun x => Real.sqrt (Δ x))
      ((deriv E t * G t + E t * deriv G t - 2 * F t * deriv F t)
        / (2 * Real.sqrt (Δ t))) t :=
    hΔ.sqrt hΔne
  rw [hsqrt.deriv]
  have hΔbound : |deriv Δ t| ≤ 2 * K * Δ t :=
    gram_det_variation_bound E F G K t hK hE hF hG hquad
  rw [hΔ.deriv] at hΔbound
  have hden : 0 < 2 * Real.sqrt (Δ t) :=
    mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sqrt_pos.mpr hpos)
  rw [abs_div, abs_of_pos hden]
  have hle :
      |deriv E t * G t + E t * deriv G t - 2 * F t * deriv F t|
        / (2 * Real.sqrt (Δ t))
        ≤ (2 * K * Δ t) / (2 * Real.sqrt (Δ t)) :=
    div_le_div_of_nonneg_right hΔbound hden.le
  refine hle.trans (le_of_eq ?_)
  have hsqrt_ne : Real.sqrt (Δ t) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hΔnn : 0 ≤ Δ t := hpos.le
  have htwo : (2 : ℝ) ≠ 0 := two_ne_zero
  calc
    (2 * K * Δ t) / (2 * Real.sqrt (Δ t))
        = (2 * (K * Δ t)) / (2 * Real.sqrt (Δ t)) := by ring
    _ = K * Δ t / Real.sqrt (Δ t) :=
        mul_div_mul_left (K * Δ t) (Real.sqrt (Δ t)) htwo
    _ = K * Real.sqrt (Δ t) := by
        rw [div_eq_iff hsqrt_ne, mul_assoc, Real.mul_self_sqrt hΔnn]
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath.Transfer
