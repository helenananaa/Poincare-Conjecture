import MorganTianLib.Ch02.SurgeryInterpolation.ProfileJets
import Mathlib
open Set
open scoped ContDiff
noncomputable section
namespace MorganTianLib.SurgeryInterpolation

/-- **Math.** A genuinely constructed flat concave profile with quantitative second-derivative dominance.
This is scalar neck data for cap construction, not a metric or a curvature theorem. -/
theorem exists_small_flat_concave_profile (L tolerance : ℝ)
    (hL : 0 < L) (htol : 0 < tolerance) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧
      (∀ s, 0 ≤ s → f s = 0) ∧
      (∀ n : ℕ, iteratedDeriv n f 0 = 0) ∧
      ∀ s ∈ Ioo (-L) 0,
        f s < 0 ∧ 0 < deriv f s ∧ deriv (deriv f) s < 0 ∧
        |f s| < tolerance ∧ |deriv f s| < tolerance ∧
        |deriv (deriv f) s| < tolerance ∧
        max |f s| |deriv f s| ≤ tolerance * |deriv (deriv f) s| := by
/- SWARM_PROOF_BEGIN -/
  let eta : ℝ := min tolerance 1
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min htol zero_lt_one
  have heta_one : eta ≤ 1 := by
    dsimp [eta]
    exact min_le_right _ _
  have heta_tol : eta ≤ tolerance := by
    dsimp [eta]
    exact min_le_left _ _

  let q : ℝ := 4 * L + 2 * L ^ 2 / eta + 1
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hq4 : 4 * L ≤ q := by
    dsimp [q]
    have h : 0 ≤ 2 * L ^ 2 / eta + 1 := by positivity
    linarith
  have hqL : 2 * L ^ 2 / eta ≤ q := by
    dsimp [q]
    have h : 0 ≤ 4 * L + 1 := by positivity
    linarith

  let g : ℝ → ℝ := neckProfile 1 q
  let F : ℝ → ℝ := fun s => -g (-s)
  have hgcd : ContDiff ℝ ∞ g := by
    exact neckProfile_contDiff 1 q
  have hneg : ContDiff ℝ ∞ (fun s : ℝ => -s) := contDiff_id.neg
  have hFcd : ContDiff ℝ ∞ F := by
    simpa [F, Function.comp_def] using hgcd.neg.comp hneg
  have hF1cd : ContDiff ℝ ∞ (deriv F) :=
    (contDiff_infty_iff_deriv.mp hFcd).2

  have hFzero : ∀ s, 0 ≤ s → F s = 0 := by
    intro s hs
    dsimp [F, g]
    rw [neckProfile_eq_zero hq (by linarith) 1]
    simp

  have hF1cont : Continuous (deriv F) := hFcd.continuous_deriv (by simp)
  have hF2cont : Continuous (deriv (deriv F)) := hF1cd.continuous_deriv (by simp)
  have hB0 : Bornology.IsBounded (F '' Icc (-L) 0) :=
    ((isCompact_Icc : IsCompact (Icc (-L) 0)).image hFcd.continuous).isBounded
  have hB1 : Bornology.IsBounded (deriv F '' Icc (-L) 0) :=
    ((isCompact_Icc : IsCompact (Icc (-L) 0)).image hF1cont).isBounded
  have hB2 : Bornology.IsBounded (deriv (deriv F) '' Icc (-L) 0) :=
    ((isCompact_Icc : IsCompact (Icc (-L) 0)).image hF2cont).isBounded
  obtain ⟨C0, hC0⟩ := hB0.subset_closedBall (0 : ℝ)
  obtain ⟨C1, hC1⟩ := hB1.subset_closedBall (0 : ℝ)
  obtain ⟨C2, hC2⟩ := hB2.subset_closedBall (0 : ℝ)
  let C : ℝ := max (max C0 C1) C2
  have hC0' : ∀ s ∈ Icc (-L) 0, |F s| ≤ C := by
    intro s hs
    have h := Metric.mem_closedBall.mp (hC0 ⟨s, hs, rfl⟩)
    have h' := h.trans ((le_max_left C0 C1).trans (le_max_left (max C0 C1) C2))
    simpa only [Real.dist_eq, sub_zero] using h'
  have hC1' : ∀ s ∈ Icc (-L) 0, |deriv F s| ≤ C := by
    intro s hs
    have h := Metric.mem_closedBall.mp (hC1 ⟨s, hs, rfl⟩)
    have h' := h.trans ((le_max_right C0 C1).trans (le_max_left (max C0 C1) C2))
    simpa only [Real.dist_eq, sub_zero] using h'
  have hC2' : ∀ s ∈ Icc (-L) 0, |deriv (deriv F) s| ≤ C := by
    intro s hs
    have h := Metric.mem_closedBall.mp (hC2 ⟨s, hs, rfl⟩)
    have h' := h.trans (le_max_right (max C0 C1) C2)
    simpa only [Real.dist_eq, sub_zero] using h'
  have hCnonneg : 0 ≤ C := by
    have h := hC0' (-L) ⟨le_rfl, by linarith⟩
    exact (abs_nonneg (F (-L))).trans h

  let amplitude : ℝ := min 1 (tolerance / (C + 1))
  have hamplitude : 0 < amplitude := by
    dsimp [amplitude]
    exact lt_min zero_lt_one (div_pos htol (by linarith))
  have hamplitude_le : amplitude ≤ tolerance / (C + 1) :=
    min_le_right _ _
  have hsmall : amplitude * C < tolerance := by
    have hden : 0 < C + 1 := by linarith
    calc
      amplitude * C ≤ tolerance / (C + 1) * C :=
        mul_le_mul_of_nonneg_right hamplitude_le hCnonneg
      _ < tolerance := by
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hden).2
        nlinarith

  let f : ℝ → ℝ := fun s => amplitude * F s
  have hf_formula : ∀ s, f s = -neckProfile amplitude q (-s) := by
    intro s
    dsimp [f, F, g, neckProfile]
    ring
  have hfcd : ContDiff ℝ ∞ f := by
    simpa [f] using ContDiff.const_smul amplitude hFcd
  have hdf : ∀ s, deriv f s = amplitude * deriv F s := by
    intro s
    have h := (hFcd.differentiable (by simp) s).hasDerivAt.const_mul amplitude
    simpa [f] using h.deriv
  have hddf : ∀ s, deriv (deriv f) s = amplitude * deriv (deriv F) s := by
    intro s
    have hderiv : deriv f = fun t => amplitude * deriv F t := funext hdf
    rw [hderiv]
    have h := (hF1cd.differentiable (by simp) s).hasDerivAt.const_mul amplitude
    simpa using h.deriv

  have hflat : ∀ n : ℕ, iteratedDeriv n f 0 = 0 := by
    intro n
    have hEq : Set.EqOn f (fun _ : ℝ => 0) (Ioi 0) := by
      intro s hs
      rw [hf_formula, neckProfile_eq_zero hq (neg_nonpos.mpr hs.le)]
      simp
    have hEqDeriv := hEq.iteratedDeriv_of_isOpen isOpen_Ioi n
    have hcont : Continuous (iteratedDeriv n f) :=
      hfcd.continuous_iteratedDeriv n (by exact_mod_cast le_top)
    refine ContinuousWithinAt.eq_const_of_mem_closure
      (hcont.continuousWithinAt :
        ContinuousWithinAt (iteratedDeriv n f) (Ioi 0) 0)
      (by simp [closure_Ioi]) ?_
    intro s hs
    simpa using hEqDeriv hs

  have hjets := neckProfile_flat_and_derivatives (1 : ℝ) q hq
  have hFderiv : ∀ s, 0 < -s →
      deriv F s = Real.exp (-q / (-s)) * q / (-s) ^ 2 := by
    intro s hs
    have hg : HasDerivAt g (Real.exp (-q / (-s)) * q / (-s) ^ 2) (-s) := by
      have h := (hgcd.differentiable (by simp) (-s)).hasDerivAt
      rw [hjets.2 (-s) hs |>.1] at h
      simpa only [one_mul] using h
    have h := (hg.comp s (hasDerivAt_neg s)).neg
    simpa [F, Function.comp_def] using h.deriv

  have hFsecond : ∀ s, 0 < -s →
      deriv (deriv F) s = -Real.exp (-q / (-s)) * q * (q - 2 * (-s)) / (-s) ^ 4 := by
    intro s hs
    have hg : HasDerivAt (deriv g)
        (Real.exp (-q / (-s)) * q * (q - 2 * (-s)) / (-s) ^ 4) (-s) := by
      have h := ((contDiff_infty_iff_deriv.mp hgcd).2.differentiable (by simp) (-s)).hasDerivAt
      rw [hjets.2 (-s) hs |>.2] at h
      simpa only [one_mul] using h
    have hcomp := hg.comp s (hasDerivAt_neg s)
    have hloc : Filter.EventuallyEq (nhds s) (deriv F) (fun t => deriv g (-t)) := by
      filter_upwards [Iio_mem_nhds (by linarith : s < 0)] with t ht
      have ht0 : t < 0 := ht
      have h := hFderiv t (by linarith)
      have hg' := h
      have hg0 := (hgcd.differentiable (by simp) (-t)).hasDerivAt
      rw [hjets.2 (-t) (by linarith) |>.1] at hg0
      simp only [one_mul] at hg0
      calc
        deriv F t = Real.exp (-q / (-t)) * q / (-t) ^ 2 := h
        _ = deriv g (-t) := by simpa only [one_mul] using hg0.deriv.symm
    have h := hcomp.congr_of_eventuallyEq hloc
    convert h.deriv using 1 <;> ring

  refine ⟨f, hfcd, ?_, hflat, ?_⟩
  · intro s hs
    rw [hf_formula, neckProfile_eq_zero hq (neg_nonpos.mpr hs)]
    simp
  · intro s hs
    have hx : 0 < -s := by linarith [hs.2]
    have hxL : -s < L := by linarith [hs.1]
    have hqhalf : q / 2 ≤ q - 2 * (-s) := by
      linarith [hq4]
    have hqminus : 0 < q - 2 * (-s) := by linarith
    have hpoly1 : (-s) ^ 2 ≤ eta * (q - 2 * (-s)) := by
      have hLsq : L ^ 2 ≤ eta * q / 2 := by
        have h := (div_le_iff₀ heta).mp hqL
        nlinarith
      have hxsq : (-s) ^ 2 < L ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hqhalf heta.le]
    have hpoly2 : (-s) ^ 4 ≤ eta * q * (q - 2 * (-s)) := by
      have hLsq : L ^ 2 ≤ eta * q / 2 := by
        have h := (div_le_iff₀ heta).mp hqL
        nlinarith
      have hxsq : (-s) ^ 2 ≤ eta * q := by
        have hxsq' : (-s) ^ 2 < L ^ 2 := by nlinarith
        nlinarith
      have hmul := mul_le_mul hpoly1 hxsq (sq_nonneg (-s))
        (by positivity : 0 ≤ eta * (q - 2 * (-s)))
      nlinarith [mul_nonneg (mul_nonneg (le_of_lt heta) (le_of_lt hqminus)) hq.le]
    have hpos : 0 < neckProfile amplitude q (-s) := by
      unfold neckProfile
      exact mul_pos hamplitude (expNegInvGlue.pos_of_pos (div_pos hx hq))
    have hfneg : f s < 0 := by
      rw [hf_formula]
      exact neg_lt_zero.mpr hpos
    have hderiv : deriv f s = amplitude *
        (Real.exp (-q / (-s)) * q / (-s) ^ 2) := by
      rw [hdf, hFderiv s hx]
    have hsecond : deriv (deriv f) s = amplitude *
        (-Real.exp (-q / (-s)) * q * (q - 2 * (-s)) / (-s) ^ 4) := by
      rw [hddf, hFsecond s hx]
    have hexp : 0 < Real.exp (-q / (-s)) := Real.exp_pos _
    have hderivpos : 0 < deriv f s := by
      rw [hderiv]
      positivity
    have hsecondneg : deriv (deriv f) s < 0 := by
      rw [hsecond]
      have hx4 : 0 < (-s) ^ 4 := by positivity
      have hcore : 0 < Real.exp (-q / (-s)) * q * (q - 2 * (-s)) /
          (-s) ^ 4 := by positivity
      have hneg : -Real.exp (-q / (-s)) * q * (q - 2 * (-s)) /
          (-s) ^ 4 < 0 := by
        convert neg_lt_zero.mpr hcore using 1 <;> ring
      exact mul_neg_of_pos_of_neg hamplitude hneg
    have habs0 : |f s| < tolerance := by
      have h := hC0' s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      calc
        |f s| = amplitude * |F s| := by
          change |amplitude * F s| = amplitude * |F s|
          rw [abs_mul, abs_of_pos hamplitude]
        _ ≤ amplitude * C := mul_le_mul_of_nonneg_left h hamplitude.le
        _ < tolerance := hsmall
    have habs1 : |deriv f s| < tolerance := by
      rw [hdf]
      have h := hC1' s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      rw [abs_mul, abs_of_pos hamplitude]
      calc
        amplitude * |deriv F s| ≤ amplitude * C :=
          mul_le_mul_of_nonneg_left h hamplitude.le
        _ < tolerance := hsmall
    have habs2 : |deriv (deriv f) s| < tolerance := by
      rw [hddf]
      have h := hC2' s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      rw [abs_mul, abs_of_pos hamplitude]
      calc
        amplitude * |deriv (deriv F) s| ≤ amplitude * C :=
          mul_le_mul_of_nonneg_left h hamplitude.le
        _ < tolerance := hsmall
    have hdominance : max |f s| |deriv f s| ≤
        tolerance * |deriv (deriv f) s| := by
      have hval : f s = -amplitude * Real.exp (-q / (-s)) := by
        rw [hf_formula]
        unfold neckProfile
        have harg : 0 < (-s) / q := div_pos hx hq
        simp only [expNegInvGlue, if_neg (not_le_of_gt harg)]
        congr 2
        field_simp [ne_of_gt hx, ne_of_gt hq]
      have habsval : |f s| = amplitude * Real.exp (-q / (-s)) := by
        rw [hval]
        have heq : -amplitude * Real.exp (-q / (-s)) =
            -(amplitude * Real.exp (-q / (-s))) := by ring
        rw [heq, abs_neg, abs_mul, abs_of_pos hamplitude, abs_of_pos hexp]
      have habsderiv : |deriv f s| =
          amplitude * (Real.exp (-q / (-s)) * q / (-s) ^ 2) := by
        rw [hderiv, abs_mul]
        rw [abs_of_pos hamplitude, abs_div, abs_of_pos (by positivity : 0 < (-s) ^ 2)]
        rw [abs_of_pos (mul_pos hexp hq)]
      have habssecond : |deriv (deriv f) s| =
          amplitude * (Real.exp (-q / (-s)) * q * (q - 2 * (-s)) / (-s) ^ 4) := by
        rw [hsecond]
        have hcore : 0 < Real.exp (-q / (-s)) * q * (q - 2 * (-s)) /
            (-s) ^ 4 := by positivity
        have heq : -Real.exp (-q / (-s)) * q * (q - 2 * (-s)) /
            (-s) ^ 4 = -(Real.exp (-q / (-s)) * q *
              (q - 2 * (-s)) / (-s) ^ 4) := by ring
        rw [heq, abs_mul, abs_of_pos hamplitude, abs_neg, abs_of_pos hcore]
      have hdom0 : |f s| ≤ eta * |deriv (deriv f) s| := by
        rw [habsval, habssecond]
        have hden : 0 < (-s) ^ 4 := by positivity
        have hratio : 1 ≤ eta * q * (q - 2 * (-s)) / (-s) ^ 4 := by
          apply (le_div_iff₀ hden).2
          simpa using hpoly2
        calc
          amplitude * Real.exp (-q / (-s)) =
              (amplitude * Real.exp (-q / (-s))) * 1 := by ring
          _ ≤ (amplitude * Real.exp (-q / (-s))) *
              (eta * q * (q - 2 * (-s)) / (-s) ^ 4) :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = eta * (amplitude *
              (Real.exp (-q / (-s)) * q * (q - 2 * (-s)) / (-s) ^ 4)) := by
            ring
      have hdom1 : |deriv f s| ≤ eta * |deriv (deriv f) s| := by
        rw [habsderiv, habssecond]
        have hden : 0 < (-s) ^ 2 := by positivity
        have hratio : 1 ≤ eta * (q - 2 * (-s)) / (-s) ^ 2 := by
          apply (le_div_iff₀ hden).2
          simpa using hpoly1
        calc
          amplitude * (Real.exp (-q / (-s)) * q / (-s) ^ 2) =
              (amplitude * (Real.exp (-q / (-s)) * q / (-s) ^ 2)) * 1 := by ring
          _ ≤ (amplitude * (Real.exp (-q / (-s)) * q / (-s) ^ 2)) *
              (eta * (q - 2 * (-s)) / (-s) ^ 2) :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = eta * (amplitude *
              (Real.exp (-q / (-s)) * q * (q - 2 * (-s)) / (-s) ^ 4)) := by
            field_simp [ne_of_gt hx]
      rw [max_le_iff]
      constructor
      · exact hdom0.trans (mul_le_mul_of_nonneg_right heta_tol
          (abs_nonneg _))
      · exact hdom1.trans (mul_le_mul_of_nonneg_right heta_tol
          (abs_nonneg _))
    exact ⟨hfneg, hderivpos, hsecondneg, habs0, habs1, habs2, hdominance⟩
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryInterpolation
