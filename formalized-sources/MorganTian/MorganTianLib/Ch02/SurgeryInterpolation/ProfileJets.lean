import MorganTianLib.Ch02.SurgeryInterpolation.ScalarProfile
import DoCarmoLib.Riemannian.Metric.RiemannianMetric

open Set Function Riemannian Bundle
open scoped ContDiff Manifold Topology Bundle
noncomputable section
namespace MorganTianLib.SurgeryInterpolation

/-- **Math.** The profile is flat at zero and has exact positive-side derivatives. -/
theorem neckProfile_flat_and_derivatives (amplitude q : ℝ) (hq : 0 < q) :
    (∀ n : ℕ, iteratedDeriv n (neckProfile amplitude q) 0 = 0) ∧
    ∀ s : ℝ, 0 < s →
      deriv (neckProfile amplitude q) s =
        amplitude * Real.exp (-q / s) * q / s ^ 2 ∧
      deriv (deriv (neckProfile amplitude q)) s =
        amplitude * Real.exp (-q / s) * q * (q - 2 * s) / s ^ 4 := by
/- SWARM_PROOF_BEGIN -/
  have hflat : ∀ n : ℕ, iteratedDeriv n (neckProfile amplitude q) 0 = 0 := by
    intro n
    have hEq : Set.EqOn (neckProfile amplitude q) (fun _ : ℝ => 0) (Iio 0) := by
      intro x hx
      exact neckProfile_eq_zero hq hx.le amplitude
    have hEqDeriv := hEq.iteratedDeriv_of_isOpen isOpen_Iio n
    have hcont : Continuous (iteratedDeriv n (neckProfile amplitude q)) :=
      (neckProfile_contDiff amplitude q).continuous_iteratedDeriv n
        (by exact_mod_cast le_top)
    refine ContinuousWithinAt.eq_const_of_mem_closure
      (hcont.continuousWithinAt :
        ContinuousWithinAt (iteratedDeriv n (neckProfile amplitude q)) (Iio 0) 0)
      (by simp [closure_Iio]) ?_
    intro x hx
    simpa using hEqDeriv hx

  have hfirst : ∀ s : ℝ, 0 < s →
      deriv (neckProfile amplitude q) s =
        amplitude * Real.exp (-q / s) * q / s ^ 2 := by
    intro s hs
    have hloc : neckProfile amplitude q =ᶠ[𝓝 s]
        (fun x : ℝ => amplitude * Real.exp (-q / x)) := by
      filter_upwards [Ioi_mem_nhds hs] with x hx
      have hxq : 0 < x / q := div_pos hx hq
      rw [neckProfile, expNegInvGlue, if_neg (not_le_of_gt hxq)]
      congr 2
      rw [inv_div, neg_div]
    have hinner : HasDerivAt (fun x : ℝ => -q / x) (q / s ^ 2) s := by
      convert! (hasDerivAt_const s (-q)).div (hasDerivAt_id s) hs.ne' using 1 <;>
        simp [Pi.div_apply, id_eq] <;> ring
    have hmodel : HasDerivAt (fun x : ℝ => amplitude * Real.exp (-q / x))
        (amplitude * (Real.exp (-q / s) * (q / s ^ 2))) s :=
      hinner.exp.const_mul amplitude
    have hderiv := (hmodel.congr_of_eventuallyEq hloc).deriv
    convert! hderiv using 1 <;> ring

  refine ⟨hflat, ?_⟩
  intro s hs
  constructor
  · exact hfirst s hs
  · have hloc : deriv (neckProfile amplitude q) =ᶠ[𝓝 s]
        (fun x : ℝ =>
          (amplitude * Real.exp (-q / x)) * (q / x ^ 2)) := by
      filter_upwards [Ioi_mem_nhds hs] with x hx
      rw [hfirst x hx]
      ring
    have hinner : HasDerivAt (fun x : ℝ => -q / x) (q / s ^ 2) s := by
      convert! (hasDerivAt_const s (-q)).div (hasDerivAt_id s) hs.ne' using 1 <;>
        simp [Pi.div_apply, id_eq] <;> ring
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-q / x))
        (Real.exp (-q / s) * (q / s ^ 2)) s :=
      hinner.exp
    have hmodel : HasDerivAt (fun x : ℝ => amplitude * Real.exp (-q / x))
        (amplitude * (Real.exp (-q / s) * (q / s ^ 2))) s :=
      hexp.const_mul amplitude
    have hpow : HasDerivAt (fun x : ℝ => q / x ^ 2) (-2 * q * s / s ^ 4) s := by
      convert! (hasDerivAt_const s q).div ((hasDerivAt_id s).pow 2)
        (pow_ne_zero 2 hs.ne') using 1 <;>
        simp [Pi.div_apply, id_eq] <;> ring
    have hprod := hmodel.mul hpow
    have hderiv := (hprod.congr_of_eventuallyEq hloc).deriv
    convert! hderiv using 1 <;> try field_simp [hs.ne'] <;> ring
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryInterpolation
