import MorganTianLib.Ch02.SurgeryCap.ProfileData
import Mathlib

open Set
open scoped ContDiff Topology
noncomputable section
namespace MorganTianLib.SurgeryCap

/-- **Math.** Uniform bounds for the two radial curvature expressions of the
constructed profile; identification with a metric's curvature is a separate theorem. -/
theorem RoundCapProfile.coefficient_control (P : RoundCapProfile) :
    (∀ r, 0 ≤ r → P.w r ≤ min r (Real.sqrt 2)) ∧
    (∀ r, 0 < r → r < P.r0 →
      P.radialCoefficient r = 1 / 4 ∧ P.tangentialCoefficient r = 1 / 4) ∧
    (∀ r, P.A < r →
      P.radialCoefficient r = 0 ∧ P.tangentialCoefficient r = 1 / 2) ∧
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r, 0 < r →
      0 ≤ P.radialCoefficient r ∧ P.radialCoefficient r ≤ C ∧
      c ≤ P.tangentialCoefficient r ∧ P.tangentialCoefficient r ≤ C := by
/- SWARM_PROOF_BEGIN -/
  classical
  have hdiff : Differentiable ℝ P.w := P.smooth.differentiable (by simp)
  have hcont : Continuous P.w := P.smooth.continuous
  have hmono : MonotoneOn P.w (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcont.continuousOn
      hdiff.differentiableOn
    intro x hx
    rw [interior_Ici] at hx
    exact (P.deriv_bounds x hx.le).1
  have hupper : ∀ {x y : ℝ}, x ∈ Ici 0 → y ∈ Ici 0 → x ≤ y →
      P.w y - P.w x ≤ 1 * (y - x) := by
    intro x y hx hy hxy
    exact (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le hcont.continuousOn
      hdiff.differentiableOn (by
        intro z hz
        rw [interior_Ici] at hz
        exact (P.deriv_bounds z hz.le).2) x hx y hy hxy
  have hw_le_r : ∀ {r : ℝ}, 0 ≤ r → P.w r ≤ r := by
    intro r hr
    have h := hupper (x := 0) (y := r) (by simp) (by exact hr) hr
    simpa [P.w_zero] using h
  have hw_le_sqrt : ∀ {r : ℝ}, 0 ≤ r → P.w r ≤ Real.sqrt 2 := by
    intro r hr
    by_cases hA : r ≤ P.A
    · have h := hmono (show r ∈ Ici 0 by exact hr) (show P.A ∈ Ici 0 by
        exact le_of_lt (lt_trans P.r0_pos P.r0_lt_A)) hA
      simpa [P.tail P.A (le_refl P.A)] using h
    · have hAr : P.A < r := lt_of_not_ge hA
      exact le_of_eq (P.tail r (le_of_lt hAr))
  have htip_deriv : ∀ r, 0 < r → r < P.r0 →
      deriv P.w r = Real.cos (r / 2) ∧
        deriv (deriv P.w) r = -(1 / 2) * Real.sin (r / 2) := by
    intro r hr hr0
    let f : ℝ → ℝ := fun x => 2 * Real.sin (x / 2)
    have heq : P.w =ᶠ[𝓝 r] f := by
      have hn : Ioo (-P.r0) P.r0 ∈ 𝓝 r :=
        Ioo_mem_nhds (by linarith) hr0
      filter_upwards [hn] with x hx
      exact P.tip x (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
    have hformula : ∀ x, deriv f x = Real.cos (x / 2) := by
      intro x
      have h := HasDerivAt.const_mul (2 : ℝ)
        ((Real.hasDerivAt_sin (x / 2)).comp x ((hasDerivAt_id x).div_const 2))
      convert h.deriv using 1 <;> simp [f, Function.comp_def] <;> ring
    have hd1 : deriv P.w r = Real.cos (r / 2) :=
      (heq.deriv_eq).trans (hformula r)
    have heq' : deriv P.w =ᶠ[𝓝 r] (fun x => Real.cos (x / 2)) :=
      heq.deriv.trans (Filter.Eventually.of_forall hformula)
    have hd2 : deriv (deriv P.w) r =
        deriv (fun x : ℝ => Real.cos (x / 2)) r := heq'.deriv_eq
    have hcos := (Real.hasDerivAt_cos (r / 2)).comp r ((hasDerivAt_id r).div_const 2)
    refine ⟨hd1, ?_⟩
    calc
      deriv (deriv P.w) r = deriv (fun x : ℝ => Real.cos (x / 2)) r := hd2
      _ = -(1 / 2) * Real.sin (r / 2) := by
        convert hcos.deriv using 1 <;> simp [Function.comp_def] <;> ring
  have htip_coeff : ∀ r, 0 < r → r < P.r0 →
      P.radialCoefficient r = 1 / 4 ∧ P.tangentialCoefficient r = 1 / 4 := by
    intro r hr hr0
    obtain ⟨hd1, hd2⟩ := htip_deriv r hr hr0
    have hw : P.w r = 2 * Real.sin (r / 2) := P.tip r (abs_le.mpr ⟨by
      linarith [P.r0_pos], hr0.le⟩)
    have hspos : 0 < Real.sin (r / 2) := by
      have hp := P.positive r hr
      rw [hw] at hp
      nlinarith
    constructor
    · rw [RoundCapProfile.radialCoefficient, hw, hd2]
      field_simp [hspos.ne']
      norm_num
    · rw [RoundCapProfile.tangentialCoefficient, hw, hd1]
      field_simp [hspos.ne']
      nlinarith [Real.sin_sq_add_cos_sq (r / 2)]
  have htail_coeff : ∀ r, P.A < r →
      P.radialCoefficient r = 0 ∧ P.tangentialCoefficient r = 1 / 2 := by
    intro r hr
    have heq : P.w =ᶠ[𝓝 r] (fun _ : ℝ => Real.sqrt 2) := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact P.tail x (le_of_lt hx)
    have hd1 : deriv P.w r = 0 := by
      simpa using heq.deriv_eq
    have heq' : deriv P.w =ᶠ[𝓝 r] (fun _ : ℝ => 0) := by
      simpa using heq.deriv
    have hd2 : deriv (deriv P.w) r = 0 := by
      simpa using heq'.deriv_eq
    have hw : P.w r = Real.sqrt 2 := P.tail r (le_of_lt hr)
    have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
    have hsqrt0 : Real.sqrt 2 ≠ 0 := by positivity
    constructor
    · simp [RoundCapProfile.radialCoefficient, hw, hd1, hd2, hsqrt0]
    · rw [RoundCapProfile.tangentialCoefficient, hw, hd1, hsqrt]
      norm_num
  have hrad_nonneg : ∀ r, 0 < r → 0 ≤ P.radialCoefficient r := by
    intro r hr
    change 0 ≤ -deriv (deriv P.w) r / P.w r
    exact div_nonneg (neg_nonneg.mpr (P.concave r hr.le)) (P.positive r hr).le
  let K : Set ℝ := Icc (P.r0 / 2) (P.A + 1)
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc
  have hKpos : ∀ x ∈ K, 0 < x := by
    intro x hx
    have hx0 : P.r0 / 2 ≤ x := hx.1
    nlinarith [P.r0_pos]
  have hKw_ne : ∀ x ∈ K, P.w x ≠ 0 := by
    intro x hx
    exact (P.positive x (hKpos x hx)).ne'
  have hcont1 : Continuous (deriv P.w) := P.smooth.continuous_deriv (by simp)
  have hcont2 : Continuous (deriv (deriv P.w)) := by
    have h2 : (2 : ℕ∞ω) ≤ ∞ :=
      (inferInstance : ENat.LEInfty (2 : ℕ∞ω)).out
    simpa [iteratedDeriv_succ] using
      (P.smooth.continuous_iteratedDeriv 2 h2)
  have hrad_cont : ContinuousOn (fun x => P.radialCoefficient x) K := by
    change ContinuousOn (fun x => -deriv (deriv P.w) x / P.w x) K
    exact hcont2.neg.continuousOn.div hcont.continuousOn hKw_ne
  have hKwsq_ne : ∀ x ∈ K, (P.w x) ^ 2 ≠ 0 := by
    intro x hx
    exact pow_ne_zero 2 (hKw_ne x hx)
  have htan_cont : ContinuousOn (fun x => P.tangentialCoefficient x) K := by
    change ContinuousOn (fun x => (1 - deriv P.w x ^ 2) / P.w x ^ 2) K
    exact (continuousOn_const.sub (hcont1.continuousOn.pow 2)).div
      (hcont.continuousOn.pow 2) hKwsq_ne
  have htan_pos : ∀ x ∈ K, 0 < P.tangentialCoefficient x := by
    intro x hx
    have hxpos := hKpos x hx
    have hdb := P.deriv_bounds x hxpos.le
    have hds := P.deriv_strict x hxpos
    rcases hdb with ⟨hd0, hd1⟩
    have hnum : 0 < 1 - deriv P.w x ^ 2 := by
      nlinarith [sq_nonneg (deriv P.w x)]
    have hden : 0 < P.w x ^ 2 := sq_pos_of_pos (P.positive x hxpos)
    change 0 < (1 - deriv P.w x ^ 2) / P.w x ^ 2
    exact div_pos hnum hden
  obtain ⟨Br, hBr⟩ := hKcompact.exists_bound_of_continuousOn hrad_cont
  obtain ⟨Bt, hBt⟩ := hKcompact.exists_bound_of_continuousOn htan_cont
  have hBr' : ∀ x ∈ K, P.radialCoefficient x ≤ Br := by
    intro x hx
    have h := hBr x hx
    have h' : |P.radialCoefficient x| ≤ Br := by
      simpa [Real.norm_eq_abs] using h
    exact (le_abs_self _).trans h'
  have hBt' : ∀ x ∈ K, P.tangentialCoefficient x ≤ Bt := by
    intro x hx
    have h := hBt x hx
    have h' : |P.tangentialCoefficient x| ≤ Bt := by
      simpa [Real.norm_eq_abs] using h
    exact (le_abs_self _).trans h'
  obtain ⟨c0, hc0, hc0le⟩ : ∃ c0 : ℝ, 0 < c0 ∧
      ∀ x ∈ K, c0 ≤ P.tangentialCoefficient x :=
    hKcompact.exists_forall_le' htan_cont htan_pos
  let c : ℝ := min c0 (1 / 4)
  let C : ℝ := max (max Br Bt) 1
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hc0 (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hc_c0 : c ≤ c0 := by
    dsimp [c]
    exact min_le_left _ _
  have hc_quarter : c ≤ (1 / 4 : ℝ) := by
    dsimp [c]
    exact min_le_right _ _
  have hBrC : Br ≤ C := by
    dsimp [C]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hBtC : Bt ≤ C := by
    dsimp [C]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hquarterC : (1 / 4 : ℝ) ≤ C := by
    dsimp [C]
    have h : (1 / 4 : ℝ) ≤ 1 := by norm_num
    exact h.trans (le_max_right _ _)
  have hhalfC : (1 / 2 : ℝ) ≤ C := by
    dsimp [C]
    have h : (1 / 2 : ℝ) ≤ 1 := by norm_num
    exact h.trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    exact le_min (hw_le_r hr) (hw_le_sqrt hr)
  · exact htip_coeff
  · exact htail_coeff
  · refine ⟨c, C, hc, hC, ?_⟩
    intro r hr
    by_cases htip : r < P.r0
    · obtain ⟨hrad, htan⟩ := htip_coeff r hr htip
      refine ⟨hrad_nonneg r hr, ?_, ?_, ?_⟩
      · rw [hrad]
        exact hquarterC
      · rw [htan]
        exact hc_quarter
      · rw [htan]
        exact hquarterC
    · by_cases htail : P.A < r
      · obtain ⟨hrad, htan⟩ := htail_coeff r htail
        refine ⟨hrad_nonneg r hr, ?_, ?_, ?_⟩
        · rw [hrad]
          exact hC.le
        · rw [htan]
          exact le_trans hc_quarter (by norm_num)
        · rw [htan]
          exact hhalfC
      · have hr0 : P.r0 ≤ r := le_of_not_gt htip
        have hrA : r ≤ P.A := le_of_not_gt htail
        have hrK : r ∈ K := by
          dsimp [K]
          constructor <;> nlinarith [P.r0_pos]
        refine ⟨hrad_nonneg r hr, ?_, ?_, ?_⟩
        · exact (hBr' r hrK).trans hBrC
        · exact hc_c0.trans (hc0le r hrK)
        · exact (hBt' r hrK).trans hBtC
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
