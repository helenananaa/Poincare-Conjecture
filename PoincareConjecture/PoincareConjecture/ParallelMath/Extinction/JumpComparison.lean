import PoincareConjecture.ParallelMath.Core
import PoincareConjecture.ParallelMath.Extinction.ExplicitDerivative
import PoincareConjecture.ParallelMath.Extinction.ComparisonInterface
import PoincareConjecture.ParallelMath.Extinction.IntegratingIdentity
import PoincareConjecture.ParallelMath.Extinction.InitialSensitivity

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath
open Set Function Filter
open scoped Topology Interval

/-- Width comparison through finitely many downward jumps, on pieces that are
actually differentiable. Uses `comparisonSolution_dominates_deriv_le`; does not
re-prove the general `finite_forward_comparison`. -/
theorem comparisonSolution_dominates_downward_jumps
    (q : ℝ → ℝ) (hq : Continuous q) (k a : ℝ)
    (n : ℕ) (time : ℕ → ℝ) (htime : StrictMono time)
    (u : ℕ → ℝ → ℝ)
    (hu : ∀ i < n, ContinuousOn (u i) (Icc (time i) (time (i + 1))))
    (hdu : ∀ i < n, ∀ t ∈ Ioo (time i) (time (i + 1)),
      ∃ u' : ℝ, HasDerivAt (u i) u' t ∧ u' ≤ -k - q t * u i t)
    (hinit : u 0 (time 0) ≤ a)
    (hjumps : ∀ i, i + 1 < n → u (i + 1) (time (i + 1)) ≤ u i (time (i + 1))) :
    ∀ i < n, ∀ t ∈ Icc (time i) (time (i + 1)),
      u i t ≤ comparisonSolution q k a (time 0) t :=
/- SWARM_PROOF_BEGIN -/
by
  set G : ℝ → ℝ := comparisonSolution q k a (time 0)
  have hGinit : G (time 0) = a :=
    (comparisonSolution_initial_and_sensitivity q k a (time 0)).1
  have hGderiv : ∀ t : ℝ, HasDerivAt G (-k - q t * G t) t :=
    fun t => comparisonSolution_hasDerivAt q hq k a (time 0) t
  have hGcont : Continuous G :=
    continuous_iff_continuousAt.2 fun t => (hGderiv t).continuousAt
  -- Integrating factor on one differentiable piece, using `G' = -k - q G`.
  have dominates : ∀ {w : ℝ → ℝ} {s t : ℝ}, s ≤ t →
      ContinuousOn w (Icc s t) →
      (∀ x ∈ Ioo s t, ∃ w' : ℝ, HasDerivAt w w' x ∧ w' ≤ -k - q x * w x) →
      w s ≤ G s → w t ≤ G t := by
    intro w s t hst hw hd hstart
    rcases eq_or_lt_of_le hst with rfl | _
    · exact hstart
    set μ : ℝ → ℝ := fun x => Real.exp (rateIntegral q s x)
    set F : ℝ → ℝ := fun x => μ x * w x
    have hμ : ∀ x, HasDerivAt μ (μ x * q x) x := fun x =>
      (hq.integral_hasStrictDerivAt s x).hasDerivAt.exp
    have hwderiv : ∀ x ∈ Ioo s t, HasDerivAt w (deriv w x) x := by
      intro x hx
      obtain ⟨w', hw'd, _⟩ := hd x hx
      exact hw'd.differentiableAt.hasDerivAt
    have hw'le : ∀ x ∈ Ioo s t, deriv w x ≤ -k - q x * w x := by
      intro x hx
      obtain ⟨w', hw'd, hle⟩ := hd x hx
      rwa [hw'd.deriv]
    set F' : ℝ → ℝ := fun x => μ x * (deriv w x + q x * w x)
    have hFderiv : ∀ x ∈ Ioo s t, HasDerivAt F (F' x) x := by
      intro x hx
      refine ((hμ x).mul (hwderiv x hx)).congr_deriv ?_
      simp only [F']
      ring
    have hF'le : ∀ x ∈ Ioo s t, F' x ≤ -k * μ x := by
      intro x hx
      have hinner : deriv w x + q x * w x ≤ -k := le_sub_iff_add_le.mp (hw'le x hx)
      calc
        F' x = μ x * (deriv w x + q x * w x) := rfl
        _ ≤ μ x * (-k) :=
          mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le
        _ = -k * μ x := by ring
    have hμcont : Continuous μ :=
      continuous_iff_continuousAt.2 fun x => (hμ x).continuousAt
    have hFcont : ContinuousOn F (Icc s t) := hμcont.continuousOn.mul hw
    have hφint : MeasureTheory.IntegrableOn (fun x => -k * μ x) (Icc s t) :=
      (hμcont.const_mul (-k)).continuousOn.integrableOn_Icc
    have hFTC :=
      intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst hFcont
        (fun x hx => (hFderiv x hx).hasDerivWithinAt) hφint hF'le
    have hμs : μ s = 1 := by simp [μ, rateIntegral, intervalIntegral.integral_same]
    have hineq : μ t * w t ≤ w s - k * ∫ x in s..t, μ x := by
      have h := hFTC
      simp [F, hμs, intervalIntegral.integral_const_mul] at h
      linarith
    have hid : μ t * G t = G s - k * ∫ x in s..t, μ x :=
      integratingFactor_identity q G hq k s t hst hGcont.continuousOn
        (fun x _hx => hGderiv x)
    have hμt_mul : μ t * w t ≤ μ t * G t :=
      hineq.trans <|
        (sub_le_sub_right hstart (k * ∫ x in s..t, μ x)).trans_eq hid.symm
    exact (mul_le_mul_iff_of_pos_left (Real.exp_pos (rateIntegral q s t))).1 hμt_mul
  have hmono : Monotone time := htime.monotone
  have interval_le : ∀ i, i < n → u i (time i) ≤ G (time i) →
      ∀ t ∈ Icc (time i) (time (i + 1)), u i t ≤ G t := by
    intro i hi hstart t ht
    refine dominates ht.1 ?_ ?_ hstart
    · exact (hu i hi).mono (Icc_subset_Icc le_rfl ht.2)
    · intro x hx
      exact hdu i hi x ⟨hx.1, hx.2.trans_le ht.2⟩
  -- Left endpoints: initial width, then previous right endpoint plus a downward jump.
  have start_le : ∀ i, i < n → u i (time i) ≤ G (time i) := by
    intro i
    induction i with
    | zero =>
      intro _hi
      exact hinit.trans_eq hGinit.symm
    | succ i ih =>
      intro hi
      have hi0 : i < n := Nat.lt_of_succ_lt hi
      have hterm : u i (time (i + 1)) ≤ G (time (i + 1)) :=
        interval_le i hi0 (ih hi0) (time (i + 1)) ⟨hmono (Nat.le_succ i), le_rfl⟩
      exact (hjumps i hi).trans hterm
  intro i hi t ht
  exact interval_le i hi (start_le i hi) t ht
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath
