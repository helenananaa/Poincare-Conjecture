import MorganTianLib.Ch02.SurgeryInterpolation.ScalarProfile
import MorganTianLib.Ch02.SurgeryInterpolation.WeightedMetric
import MorganTianLib.Ch02.SurgeryInterpolation.TipFlattening

open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryInterpolation

/-- **Math.** Tip cutoff supported strictly before the potentially singular tip coordinate. -/
def tipWeight (a b r : ℝ) : ℝ := 1 - Real.smoothTransition (2 * (r - a) / (b - a))

/-- **Math.** The conformal factor is exactly constant before the tip is reached. -/
def tipCoefficient (a b amplitude q r : ℝ) : ℝ :=
  tipWeight a b r * Real.exp (-2 * neckProfile amplitude q r) +
    (1 - tipWeight a b r) * Real.exp (-2 * neckProfile amplitude q b)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Smooth conformal modification through a nonsmooth radial tip coordinate.
The original cap metric is input; no cap-existence or curvature assertion is hidden here. -/
theorem exists_tip_smoothed_metric (g0 : RiemannianMetric I M)
    (s : M → ℝ) (a b amplitude q eta : ℝ) (hab : a < b)
    (hs : Continuous s) (hsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ s {x | s x < b})
    (ha : 0 ≤ amplitude) (hq : 0 < q) (heta : 0 < eta) :
    ∃ gh : RiemannianMetric I M,
      (∀ x v w, gh.metricInner x v w = eta * tipCoefficient a b amplitude q (s x) *
        g0.metricInner x v w) ∧
      (∀ x, s x ≤ a → ∀ v w, gh.metricInner x v w =
        eta * Real.exp (-2 * neckProfile amplitude q (s x)) * g0.metricInner x v w) ∧
      (∀ x, (a + b) / 2 ≤ s x → ∀ v w, gh.metricInner x v w =
        eta * Real.exp (-2 * neckProfile amplitude q b) * g0.metricInner x v w) ∧
      (∀ x v, gh.metricInner x v v ≤ eta * g0.metricInner x v v) := by
/- SWARM_PROOF_BEGIN -/
  have hba : 0 < b - a := sub_pos.mpr hab
  have hweight : ∀ r, tipWeight a b r ∈ Set.Icc (0 : ℝ) 1 := by
    intro r
    have h0 := Real.smoothTransition.nonneg (2 * (r - a) / (b - a))
    have h1 := Real.smoothTransition.le_one (2 * (r - a) / (b - a))
    constructor <;> dsimp [tipWeight] <;> linarith
  have hweight_contDiff : ContDiff ℝ ∞ (tipWeight a b) := by
    exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (contDiff_id.sub contDiff_const)).div_const (b - a)))
  have hprofile_exp_contDiff : ContDiff ℝ ∞
      (fun r : ℝ => Real.exp (-2 * neckProfile amplitude q r)) := by
    exact Real.contDiff_exp.comp
      (contDiff_const.mul (neckProfile_contDiff amplitude q))
  have hcoefficient_contDiff : ContDiff ℝ ∞
      (tipCoefficient a b amplitude q) := by
    exact (hweight_contDiff.mul hprofile_exp_contDiff).add
      ((contDiff_const.sub hweight_contDiff).mul contDiff_const)
  have hweight_left : ∀ {r : ℝ}, r ≤ a → tipWeight a b r = 1 := by
    intro r hr
    have harg : 2 * (r - a) / (b - a) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith
      · exact hba.le
    unfold tipWeight
    rw [Real.smoothTransition.zero_of_nonpos harg, sub_zero]
  have hweight_right : ∀ {r : ℝ}, (a + b) / 2 ≤ r → tipWeight a b r = 0 := by
    intro r hr
    have harg : 1 ≤ 2 * (r - a) / (b - a) := by
      apply (le_div_iff₀ hba).2
      nlinarith
    unfold tipWeight
    rw [Real.smoothTransition.one_of_one_le harg, sub_self]
  have hcoefficient_left : ∀ {r : ℝ}, r ≤ a →
      tipCoefficient a b amplitude q r = Real.exp (-2 * neckProfile amplitude q r) := by
    intro r hr
    rw [tipCoefficient, hweight_left hr]
    ring
  have hcoefficient_right : ∀ {r : ℝ}, (a + b) / 2 ≤ r →
      tipCoefficient a b amplitude q r = Real.exp (-2 * neckProfile amplitude q b) := by
    intro r hr
    rw [tipCoefficient, hweight_right hr]
    ring
  have hcoefficient_pos : ∀ r, 0 < tipCoefficient a b amplitude q r := by
    intro r
    have hw := hweight r
    have he0 : 0 < Real.exp (-2 * neckProfile amplitude q r) := Real.exp_pos _
    have he1 : 0 < Real.exp (-2 * neckProfile amplitude q b) := Real.exp_pos _
    by_cases hwp : 0 < tipWeight a b r
    · have hleft : 0 < tipWeight a b r * Real.exp (-2 * neckProfile amplitude q r) :=
        mul_pos hwp he0
      have hright : 0 ≤ (1 - tipWeight a b r) *
          Real.exp (-2 * neckProfile amplitude q b) :=
        mul_nonneg (sub_nonneg.mpr hw.2) (le_of_lt he1)
      rw [tipCoefficient]
      linarith
    · have hw0 : tipWeight a b r = 0 :=
        le_antisymm (le_of_not_gt hwp) hw.1
      rw [tipCoefficient, hw0]
      simpa using he1
  have hexp_le_one : ∀ r, Real.exp (-2 * neckProfile amplitude q r) ≤ 1 := by
    intro r
    apply Real.exp_le_one_iff.mpr
    nlinarith [neckProfile_nonneg ha q r]
  have hcoefficient_le_one : ∀ r, tipCoefficient a b amplitude q r ≤ 1 := by
    intro r
    have hw := hweight r
    have hleft := mul_le_mul_of_nonneg_left (hexp_le_one r) hw.1
    have hright := mul_le_mul_of_nonneg_left (hexp_le_one b) (sub_nonneg.mpr hw.2)
    rw [tipCoefficient]
    nlinarith
  have hmidb : (a + b) / 2 < b := by linarith
  have hcoeff_comp : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (tipCoefficient a b amplitude q ∘ s) := by
    apply contMDiff_comp_of_flattened_tip s (tipCoefficient a b amplitude q)
      (a := (a + b) / 2) (b := b)
      (c := Real.exp (-2 * neckProfile amplitude q b))
      hmidb hs hsmooth hcoefficient_contDiff
    exact fun r hr => hcoefficient_right hr
  let c : M → ℝ := fun x => eta * tipCoefficient a b amplitude q (s x)
  have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ c := by
    change ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => eta * (tipCoefficient a b amplitude q ∘ s) x)
    exact (contMDiff_const (I := I) (I' := 𝓘(ℝ, ℝ)) (n := ∞)).mul hcoeff_comp
  obtain ⟨gh, hgh⟩ := exists_weighted_riemannianMetric g0 g0 c (fun _ => 0)
    hc contMDiff_const
    (fun x => mul_nonneg heta.le (hcoefficient_pos (s x)).le)
    (fun _ => le_rfl)
    (fun x => by simpa [c] using mul_pos heta (hcoefficient_pos (s x)))
  refine ⟨gh, ?_, ?_, ?_, ?_⟩
  · intro x v w
    rw [hgh]
    dsimp [c]
    ring
  · intro x hx v w
    rw [hgh]
    dsimp [c]
    rw [hcoefficient_left hx]
    ring
  · intro x hx v w
    rw [hgh]
    dsimp [c]
    rw [hcoefficient_right hx]
    ring
  · intro x v
    rw [hgh]
    have hmetric : 0 ≤ g0.metricInner x v v := g0.metricInner_self_nonneg x v
    have hc_le : eta * tipCoefficient a b amplitude q (s x) ≤ eta := by
      simpa using mul_le_mul_of_nonneg_left (hcoefficient_le_one (s x)) heta.le
    have hmul := mul_le_mul_of_nonneg_right hc_le hmetric
    simpa [c] using hmul
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryInterpolation
