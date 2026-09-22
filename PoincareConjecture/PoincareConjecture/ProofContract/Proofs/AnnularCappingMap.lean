import PoincareConjecture.ProofContract.Proofs.CoordinateOpenExterior
import PoincareConjecture.ProofContract.Proofs.ShrunkCoordinateComplement
import PoincareConjecture.ProofContract.Proofs.CompactChartSqueeze
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.Proofs.RelativeCompactCollapse
import PoincareConjecture.ProofContract.Proofs.MarkedCollapseRecognition
import PoincareConjecture.ProofContract.Proofs.ConnectedSumSphereReduction
import Mathlib
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology Manifold ContDiff
/-- A concrete cap map on the closed half-radius exterior collapses only the outer three-quarter exterior. -/
theorem annular_capping_single_fiber (M : ClosedThreeManifold.{u}) (a : CoordinateBall M) :
    let C := {x : M // x ∉ a.parametrization '' Metric.ball (0:Euclidean3) (1/2)}
    let K : Set C := {x | (x:M) ∉ a.parametrization '' Metric.ball (0:Euclidean3) (3/4)}
    ∃ f : C → DoubleBall.Ball, Continuous f ∧ Surjective f ∧
      (∀ x y, f x=f y ↔ x=y ∨ (x∈K ∧ y∈K)) ∧
      ∀ (s : Sphere2) (x : C), (x:M)=a.parametrization ((1/2:ℝ) • (s:Euclidean3)) →
        (f x:Euclidean3)=(s:Euclidean3) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let C : Type u :=
    {x : M // x ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (1 / 2)}
  let K : Set C := {x | (x : M) ∉ a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)}
  change ∃ f : C → DoubleBall.Ball, Continuous f ∧ Surjective f ∧
    (∀ x y, f x = f y ↔ x = y ∨ (x ∈ K ∧ y ∈ K)) ∧
      ∀ (s : Sphere2) (x : C), (x : M) =
        a.parametrization ((1 / 2 : ℝ) • (s : Euclidean3)) →
          (f x : Euclidean3) = (s : Euclidean3)
  have hsource34 : Metric.closedBall (0 : Euclidean3) (3 / 4) ⊆
      a.parametrization.source := by
    intro z hz
    apply a.contains_two
    have hz' : ‖z‖ ≤ (3 / 4 : ℝ) := by
      simpa [Metric.mem_closedBall] using hz
    simpa [Metric.mem_closedBall] using (show ‖z‖ ≤ (2 : ℝ) by linarith)
  have hsource12 : Metric.closedBall (0 : Euclidean3) (1 / 2) ⊆
      a.parametrization.source := by
    intro z hz
    apply a.contains_two
    have hz' : ‖z‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall] using hz
    simpa [Metric.mem_closedBall] using (show ‖z‖ ≤ (2 : ℝ) by linarith)
  have hcont34 : ContinuousOn a.parametrization
      (Metric.closedBall (0 : Euclidean3) (3 / 4)) :=
    a.parametrization.continuousOn.mono hsource34
  have hcompact34 : IsCompact
      (a.parametrization '' Metric.closedBall (0 : Euclidean3) (3 / 4)) :=
    (isCompact_closedBall (0 : Euclidean3) (3 / 4)).image_of_continuousOn hcont34
  have hclosed34 : IsClosed
      (a.parametrization '' Metric.closedBall (0 : Euclidean3) (3 / 4)) :=
    hcompact34.isClosed
  have hopen34 : IsOpen
      (a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)) := by
    apply a.parametrization.isOpen_image_of_subset_source Metric.isOpen_ball
    exact Metric.ball_subset_closedBall.trans hsource34
  let U : Set C := (fun x : C => (x : M)) ⁻¹'
    (a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4))
  let A : Set C := (fun x : C => (x : M)) ⁻¹'
    (a.parametrization '' Metric.closedBall (0 : Euclidean3) (3 / 4))
  have hUopen : IsOpen U := by
    change IsOpen ((fun x : C => (x : M)) ⁻¹'
      (a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)))
    exact hopen34.preimage continuous_subtype_val
  have hAclosed : IsClosed A := by
    change IsClosed ((fun x : C => (x : M)) ⁻¹'
      (a.parametrization '' Metric.closedBall (0 : Euclidean3) (3 / 4)))
    exact hclosed34.preimage continuous_subtype_val
  have hUsubA : U ⊆ A := by
    intro x hx
    exact image_mono Metric.ball_subset_closedBall hx
  have hclosureU : closure U ⊆ A :=
    closure_minimal hUsubA hAclosed
  have hcoord : ∀ x : C, x ∈ closure U →
      ∃ z : Euclidean3, z ∈ Metric.closedBall 0 (3 / 4) ∧
        a.parametrization z = (x : M) ∧ (1 / 2 : ℝ) ≤ ‖z‖ := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hclosureU hx
    have hzsource : z ∈ a.parametrization.source := hsource34 hz
    have hnormlower : (1 / 2 : ℝ) ≤ ‖z‖ := by
      by_contra hn
      have hzlt : ‖z‖ < (1 / 2 : ℝ) := lt_of_not_ge hn
      apply x.property
      exact ⟨z, by simpa [Metric.mem_ball] using hzlt, hzx⟩
    exact ⟨z, hz, hzx, hnormlower⟩
  let q : C → Euclidean3 := fun x => a.parametrization.symm (x : M)
  have hqeq : ∀ x : C, x ∈ closure U → ∃ z : Euclidean3,
      z ∈ Metric.closedBall 0 (3 / 4) ∧
        q x = z ∧ a.parametrization z = (x : M) ∧ (1 / 2 : ℝ) ≤ ‖z‖ := by
    intro x hx
    obtain ⟨z, hz, hzx, hzlower⟩ := hcoord x hx
    have hzsource : z ∈ a.parametrization.source := hsource34 hz
    have hsymm : q x = z := by
      dsimp [q]
      rw [← hzx]
      exact a.parametrization.left_inv hzsource
    exact ⟨z, hz, hsymm, hzx, hzlower⟩
  have hq_cont : ContinuousOn q (closure U) := by
    rw [continuousOn_iff_continuous_restrict]
    let g : closure U → M := fun x => (x : C)
    have hg : Continuous g := by
      exact continuous_subtype_val.comp continuous_subtype_val
    have hc : Continuous (fun x : closure U =>
        a.parametrization.symm (g x)) := by
      apply a.parametrization.continuousOn_symm.comp_continuous hg
      intro x
      obtain ⟨z, hz, _, hzx, _⟩ := hqeq x.1 x.2
      simpa [g, hzx] using a.parametrization.map_source (hsource34 hz)
    change Continuous (fun x : closure U =>
      a.parametrization.symm ((x : C) : M))
    exact hc
  let ρ : C → ℝ := fun x => ‖q x‖
  let r : C → ℝ := fun x => min 1 (max 0 (3 - 4 * ρ x))
  let n : C → Euclidean3 := fun x => (ρ x)⁻¹ • q x
  have hρ_bounds : ∀ x : C, x ∈ closure U →
      (1 / 2 : ℝ) ≤ ρ x ∧ ρ x ≤ (3 / 4 : ℝ) := by
    intro x hx
    obtain ⟨z, hz, hqz, _, hzlower⟩ := hqeq x hx
    have hzupper : ‖z‖ ≤ (3 / 4 : ℝ) := by
      simpa [Metric.mem_closedBall] using hz
    exact ⟨by simpa [ρ, hqz] using hzlower, by simpa [ρ, hqz] using hzupper⟩
  have hinj34 : Set.InjOn a.parametrization
      (Metric.closedBall (0 : Euclidean3) (3 / 4)) := by
    intro z hz w hw hzw
    have h := congrArg a.parametrization.symm hzw
    simpa only [a.parametrization.left_inv (hsource34 hz),
      a.parametrization.left_inv (hsource34 hw)] using h
  have hCmem : ∀ z : Euclidean3, z ∈ Metric.closedBall 0 (3 / 4) →
      (1 / 2 : ℝ) ≤ ‖z‖ →
        a.parametrization z ∉ a.parametrization '' Metric.ball 0 (1 / 2) := by
    intro z hz hzlower hx
    rcases hx with ⟨w, hw, hwz⟩
    have hwlt : ‖w‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball] using hw
    have hwclosed : w ∈ Metric.closedBall (0 : Euclidean3) (3 / 4) := by
      have hwle : ‖w‖ ≤ (3 / 4 : ℝ) := by linarith
      simpa [Metric.mem_closedBall] using hwle
    have hwz' : w = z := hinj34 hwclosed hz hwz
    have : ‖z‖ < (1 / 2 : ℝ) := by simpa [hwz'] using hwlt
    exact (not_lt_of_ge hzlower) this
  have hKmem : ∀ z : Euclidean3, z ∈ Metric.closedBall 0 (3 / 4) →
      ‖z‖ = (3 / 4 : ℝ) →
        a.parametrization z ∉ a.parametrization '' Metric.ball 0 (3 / 4) := by
    intro z hz hzeq hx
    rcases hx with ⟨w, hw, hwz⟩
    have hwlt : ‖w‖ < (3 / 4 : ℝ) := by
      simpa [Metric.mem_ball] using hw
    have hwclosed : w ∈ Metric.closedBall (0 : Euclidean3) (3 / 4) :=
      Metric.ball_subset_closedBall hw
    have hwz' : w = z := hinj34 hwclosed hz hwz
    have : ‖z‖ < (3 / 4 : ℝ) := by simpa [hwz'] using hwlt
    exact (lt_irrefl (3 / 4 : ℝ)) (hzeq ▸ this)
  have hU_r : ∀ x : C, x ∈ U → r x = 3 - 4 * ρ x := by
    intro x hx
    have hb := hρ_bounds x (subset_closure hx)
    have hnonneg : 0 ≤ (3 : ℝ) - 4 * ρ x := by linarith
    have hleone : (3 : ℝ) - 4 * ρ x ≤ 1 := by linarith
    dsimp [r]
    rw [max_eq_right hnonneg, min_eq_right hleone]
  have hρ_nonneg : ∀ x : C, 0 ≤ ρ x := by
    intro x
    exact norm_nonneg _
  have hr_nonneg : ∀ x : C, 0 ≤ r x := by
    intro x
    dsimp [r]
    exact le_min (by norm_num) (le_max_left _ _)
  have hr_le_one : ∀ x : C, r x ≤ 1 := by
    intro x
    exact min_le_left _ _
  have hn_le_one : ∀ x : C, ‖n x‖ ≤ 1 := by
    intro x
    by_cases hx : q x = 0
    · simp [n, ρ, hx]
    · have hxpos : 0 < ‖q x‖ := norm_pos_iff.mpr hx
      dsimp [n]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr hxpos.le), inv_mul_cancel₀ hxpos.ne']
  have hn_norm : ∀ x : C, q x ≠ 0 → ‖n x‖ = 1 := by
    intro x hx
    have hxpos : 0 < ‖q x‖ := norm_pos_iff.mpr hx
    dsimp [n]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hxpos.le), inv_mul_cancel₀ hxpos.ne']
  have hq_from_n : ∀ x : C, q x ≠ 0 → q x = ρ x • n x := by
    intro x hx
    have hxpos : 0 < ρ x := norm_pos_iff.mpr hx
    dsimp [n]
    rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  let zero : DoubleBall.Ball := ⟨0, by simp [Metric.mem_closedBall]⟩
  let f₀ : C → DoubleBall.Ball := fun x =>
    ⟨r x • n x, by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (hr_nonneg x)]
      have hmul : r x * ‖n x‖ ≤ (1 : ℝ) * 1 :=
        mul_le_mul (hr_le_one x) (hn_le_one x) (norm_nonneg _) (by norm_num)
      simpa using hmul⟩
  have hρ_cont : ContinuousOn ρ (closure U) := by
    dsimp [ρ]
    exact continuous_norm.comp_continuousOn hq_cont
  have hraw_cont : ContinuousOn (fun x : C => (3 : ℝ) - 4 * ρ x)
      (closure U) := by
    exact continuousOn_const.sub (continuousOn_const.mul hρ_cont)
  have hr_cont : ContinuousOn r (closure U) := by
    have hphi : Continuous (fun t : ℝ => min 1 (max 0 (3 - 4 * t))) := by
      exact continuous_const.min (continuous_const.max
        (continuous_const.sub (continuous_const.mul continuous_id)))
    simpa [r, Function.comp_def] using hphi.comp_continuousOn hρ_cont
  have hρ_ne : ∀ x : C, x ∈ closure U → ρ x ≠ 0 := by
    intro x hx
    have h := hρ_bounds x hx
    linarith
  have hinv_cont : ContinuousOn (fun x : C => (ρ x)⁻¹) (closure U) :=
    hρ_cont.inv₀ hρ_ne
  have hn_cont : ContinuousOn n (closure U) := by
    dsimp [n]
    exact hinv_cont.smul hq_cont
  have hf₀ : ContinuousOn f₀ (closure U) := by
    rw [continuousOn_iff_continuous_restrict]
    have hr' : Continuous (fun x : closure U => r x) :=
      continuousOn_iff_continuous_restrict.mp hr_cont
    have hn' : Continuous (fun x : closure U => n x) :=
      continuousOn_iff_continuous_restrict.mp hn_cont
    let F : closure U → DoubleBall.Ball := fun x =>
      ⟨r x • n x, by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (hr_nonneg x)]
        have hmul : r x * ‖n x‖ ≤ (1 : ℝ) * 1 :=
          mul_le_mul (hr_le_one x) (hn_le_one x) (norm_nonneg _) (by norm_num)
        simpa using hmul⟩
    have hF : Continuous F := (hr'.smul hn').subtype_mk _
    convert hF using 1
    ext x
    rfl
  have hfrontier_zero : ∀ x ∈ frontier U, f₀ x = zero := by
    intro x hx
    obtain ⟨z, hz, hqz, hzx, _⟩ := hqeq x (frontier_subset_closure hx)
    have hxnot : x ∉ U := by
      intro hxin
      exact (disjoint_frontier_iff_isOpen.mpr hUopen).le_bot ⟨hx, hxin⟩
    have hzupper : ‖z‖ ≤ (3 / 4 : ℝ) := by
      simpa [Metric.mem_closedBall] using hz
    have hznotlt : ¬ ‖z‖ < (3 / 4 : ℝ) := by
      intro hzlt
      apply hxnot
      exact ⟨z, by simpa [Metric.mem_ball] using hzlt, hzx⟩
    have hzeq : ‖z‖ = (3 / 4 : ℝ) := le_antisymm hzupper (le_of_not_gt hznotlt)
    have hρeq : ρ x = (3 / 4 : ℝ) := by simpa [ρ, hqz, hzeq]
    have hreq : r x = 0 := by
      norm_num [r, hρeq]
    apply Subtype.ext
    simp [f₀, zero, hreq]
  let f : C → DoubleBall.Ball := Set.piecewise U f₀ (fun _ => zero)
  have hf : Continuous f := by
    change Continuous (Set.piecewise U f₀ (fun _ => zero))
    exact continuous_piecewise hfrontier_zero hf₀ continuous_const.continuousOn
  have hnotU_of_K : ∀ x : C, x ∈ K → x ∉ U := by
    intro x hxK hxU
    change (x : M) ∉ a.parametrization '' Metric.ball 0 (3 / 4) at hxK
    change (x : M) ∈ a.parametrization '' Metric.ball 0 (3 / 4) at hxU
    exact hxK hxU
  have hK_of_notU : ∀ x : C, x ∉ U → x ∈ K := by
    intro x hxU
    change (x : M) ∉ a.parametrization '' Metric.ball 0 (3 / 4)
    intro hximage
    apply hxU
    change (x : M) ∈ a.parametrization '' Metric.ball 0 (3 / 4)
    exact hximage
  have hU_strict : ∀ x : C, x ∈ U → ρ x < (3 / 4 : ℝ) := by
    intro x hxU
    change (x : M) ∈ a.parametrization '' Metric.ball 0 (3 / 4) at hxU
    obtain ⟨z, hz, hzx⟩ := hxU
    have hzsource : z ∈ a.parametrization.source :=
      hsource34 (Metric.ball_subset_closedBall hz)
    have hqz : q x = z := by
      dsimp [q]
      rw [← hzx]
      exact a.parametrization.left_inv hzsource
    have hzlt : ‖z‖ < (3 / 4 : ℝ) := by
      simpa [Metric.mem_ball] using hz
    simpa [ρ, hqz] using hzlt
  have hU_rpos : ∀ x : C, x ∈ U → 0 < 3 - 4 * ρ x := by
    intro x hxU
    linarith [hU_strict x hxU]
  have hfU_val : ∀ x : C, x ∈ U →
      (f x : Euclidean3) = (3 - 4 * ρ x) • n x := by
    intro x hxU
    rw [show f x = f₀ x by simp [f, hxU]]
    change r x • n x = _
    rw [hU_r x hxU]
  have hf_notU_val : ∀ x : C, x ∉ U → (f x : Euclidean3) = 0 := by
    intro x hxU
    rw [show f x = zero by simp [f, hxU]]
  have hfU_nonzero : ∀ x : C, x ∈ U →
      (f x : Euclidean3) ≠ 0 := by
    intro x hxU hzero
    have hqne : q x ≠ 0 := by
      intro hqzero
      apply hρ_ne x (subset_closure hxU)
      simp [ρ, hqzero]
    have hnormeq := congrArg norm (hfU_val x hxU)
    rw [hzero, norm_zero, norm_smul,
      Real.norm_of_nonneg (le_of_lt (hU_rpos x hxU)), hn_norm x hqne,
      mul_one] at hnormeq
    linarith [hU_rpos x hxU]
  have hsurj : Surjective f := by
    intro y
    by_cases hy0 : (y : Euclidean3) = 0
    · obtain ⟨s0, hs0⟩ : (Metric.sphere (0 : Euclidean3) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr zero_le_one
      have hs0norm : ‖(s0 : Euclidean3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hs0
      let z0 : Euclidean3 := (3 / 4 : ℝ) • (s0 : Euclidean3)
      have hz0norm : ‖z0‖ = (3 / 4 : ℝ) := by
        dsimp [z0]
        rw [norm_smul, Real.norm_of_nonneg (by norm_num), hs0norm, mul_one]
      have hz0closed : z0 ∈ Metric.closedBall (0 : Euclidean3) (3 / 4) := by
        rw [Metric.mem_closedBall, dist_zero_right, hz0norm]
      let x0 : C := ⟨a.parametrization z0,
        hCmem z0 hz0closed (by linarith [hz0norm])⟩
      have hx0K : x0 ∈ K := by
        change a.parametrization z0 ∉
          a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)
        exact hKmem z0 hz0closed hz0norm
      have hx0notU : x0 ∉ U := hnotU_of_K x0 hx0K
      have hfx0 : f x0 = zero := by
        simp [f, hx0notU]
      have hyzero : y = zero := by
        apply Subtype.ext
        simpa [zero] using hy0
      rw [hyzero]
      exact ⟨x0, hfx0⟩
    · have hypos : 0 < ‖(y : Euclidean3)‖ := norm_pos_iff.mpr hy0
      have hynormle : ‖(y : Euclidean3)‖ ≤ 1 := by
        have hdist : dist (y : Euclidean3) 0 ≤ 1 := by
          simpa only [Metric.mem_closedBall] using y.property
        simpa only [dist_zero_right] using hdist
      let t : ℝ := (3 - ‖(y : Euclidean3)‖) / 4
      have htlow : (1 / 2 : ℝ) ≤ t := by
        dsimp [t]
        linarith
      have htpos : 0 < t := lt_of_lt_of_le (by norm_num) htlow
      have hthigh : t < (3 / 4 : ℝ) := by
        dsimp [t]
        linarith
      let s : Sphere2 := ⟨(‖(y : Euclidean3)‖)⁻¹ • (y : Euclidean3), by
        rw [Metric.mem_sphere, dist_zero_right, norm_smul]
        simp [Real.norm_eq_abs, abs_of_pos hypos, hypos.ne']⟩
      have hs_norm : ‖(s : Euclidean3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using s.property
      let z : Euclidean3 := t • (s : Euclidean3)
      have hz_norm : ‖z‖ = t := by
        dsimp [z]
        rw [norm_smul, Real.norm_of_nonneg htpos.le, hs_norm, mul_one]
      have hz_closed : z ∈ Metric.closedBall (0 : Euclidean3) (3 / 4) := by
        rw [Metric.mem_closedBall, dist_zero_right, hz_norm]
        exact hthigh.le
      let x : C := ⟨a.parametrization z,
        hCmem z hz_closed (by rw [hz_norm]; exact htlow)⟩
      have hxU : x ∈ U := by
        change a.parametrization z ∈
          a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)
        refine ⟨z, ?_, rfl⟩
        simpa [Metric.mem_ball, dist_zero_right, hz_norm] using hthigh
      have hzsource : z ∈ a.parametrization.source := hsource34 hz_closed
      have hqzx : q x = z := by
        dsimp [q]
        rw [a.parametrization.left_inv hzsource]
      have hρx : ρ x = t := by
        simp [ρ, hqzx, hz_norm]
      have hnx : n x = (s : Euclidean3) := by
        dsimp [n]
        rw [hρx, hqzx, show z = t • (s : Euclidean3) by rfl,
          smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
      have hrx : r x = ‖(y : Euclidean3)‖ := by
        rw [hU_r x hxU, hρx]
        dsimp [t]
        ring
      have hfx : f x = y := by
        apply Subtype.ext
        change (f x : Euclidean3) = (y : Euclidean3)
        rw [hfU_val x hxU, ← hU_r x hxU, hrx, hnx]
        dsimp [s]
        rw [smul_smul, mul_inv_cancel₀ hypos.ne', one_smul]
      exact ⟨x, hfx⟩
  have hU_coord : ∀ x : C, x ∈ U →
      q x ∈ a.parametrization.source ∧
        a.parametrization (q x) = (x : M) := by
    intro x hxU
    obtain ⟨z, hz, hqz, hzx, _⟩ := hqeq x (subset_closure hxU)
    constructor
    · rw [hqz]
      exact hsource34 hz
    · rw [hqz]
      exact hzx
  have hfiber : ∀ x y : C, f x = f y ↔
      x = y ∨ (x ∈ K ∧ y ∈ K) := by
    intro x y
    constructor
    · intro hxy
      by_cases hxU : x ∈ U
      · by_cases hyU : y ∈ U
        · have hqxne : q x ≠ 0 := by
            intro hqzero
            apply hρ_ne x (subset_closure hxU)
            simp [ρ, hqzero]
          have hqyne : q y ≠ 0 := by
            intro hqzero
            apply hρ_ne y (subset_closure hyU)
            simp [ρ, hqzero]
          have hvec : (3 - 4 * ρ x) • n x =
              (3 - 4 * ρ y) • n y := by
            have h := congrArg (fun w : DoubleBall.Ball => (w : Euclidean3)) hxy
            rw [hfU_val x hxU, hfU_val y hyU] at h
            exact h
          have hnxnorm : ‖(3 - 4 * ρ x) • n x‖ = 3 - 4 * ρ x := by
            rw [norm_smul, Real.norm_of_nonneg (le_of_lt (hU_rpos x hxU)),
              hn_norm x hqxne, mul_one]
          have hnynorm : ‖(3 - 4 * ρ y) • n y‖ = 3 - 4 * ρ y := by
            rw [norm_smul, Real.norm_of_nonneg (le_of_lt (hU_rpos y hyU)),
              hn_norm y hqyne, mul_one]
          have hnormeq : 3 - 4 * ρ x = 3 - 4 * ρ y := by
            calc
              3 - 4 * ρ x = ‖(3 - 4 * ρ x) • n x‖ := hnxnorm.symm
              _ = ‖(3 - 4 * ρ y) • n y‖ := congrArg norm hvec
              _ = 3 - 4 * ρ y := hnynorm
          have hρeq : ρ x = ρ y := by
            linarith
          have hnxy : n x = n y := by
            have hvec' : (3 - 4 * ρ x) • n x =
                (3 - 4 * ρ x) • n y := by
              simpa [hρeq] using hvec
            have hc := congrArg
              (fun w : Euclidean3 => (3 - 4 * ρ x)⁻¹ • w) hvec'
            simpa [smul_smul, inv_mul_cancel₀ (hU_rpos x hxU).ne', one_smul] using hc
          have hqxy : q x = q y := by
            calc
              q x = ρ x • n x := hq_from_n x hqxne
              _ = ρ x • n y := by rw [hnxy]
              _ = ρ y • n y := by rw [hρeq]
              _ = q y := (hq_from_n y hqyne).symm
          have hpx := (hU_coord x hxU).2
          have hpy := (hU_coord y hyU).2
          left
          apply Subtype.ext
          calc
            (x : M) = a.parametrization (q x) := hpx.symm
            _ = a.parametrization (q y) := congrArg a.parametrization hqxy
            _ = (y : M) := hpy
        · exfalso
          apply hfU_nonzero x hxU
          calc
            (f x : Euclidean3) = (f y : Euclidean3) :=
              congrArg (fun w : DoubleBall.Ball => (w : Euclidean3)) hxy
            _ = 0 := hf_notU_val y hyU
      · by_cases hyU : y ∈ U
        · exfalso
          apply hfU_nonzero y hyU
          calc
            (f y : Euclidean3) = (f x : Euclidean3) :=
              congrArg (fun w : DoubleBall.Ball => (w : Euclidean3)) hxy.symm
            _ = 0 := hf_notU_val x hxU
        · right
          exact ⟨hK_of_notU x hxU, hK_of_notU y hyU⟩
    · intro hxy
      rcases hxy with rfl | ⟨hxK, hyK⟩
      · rfl
      · have hxU : x ∉ U := hnotU_of_K x hxK
        have hyU : y ∉ U := hnotU_of_K y hyK
        simp [f, hxU, hyU]
  have hboundary : ∀ (s : Sphere2) (x : C),
      (x : M) = a.parametrization ((1 / 2 : ℝ) • (s : Euclidean3)) →
        (f x : Euclidean3) = (s : Euclidean3) := by
    intro s x hxeq
    have hs_norm : ‖(s : Euclidean3)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using s.property
    let z : Euclidean3 := (1 / 2 : ℝ) • (s : Euclidean3)
    have hz_norm : ‖z‖ = (1 / 2 : ℝ) := by
      dsimp [z]
      rw [norm_smul, Real.norm_of_nonneg (by norm_num), hs_norm, mul_one]
    have hz_closed : z ∈ Metric.closedBall (0 : Euclidean3) (3 / 4) := by
      rw [Metric.mem_closedBall, dist_zero_right, hz_norm]
      norm_num
    have hzsource : z ∈ a.parametrization.source := hsource34 hz_closed
    have hxU : x ∈ U := by
      change (x : M) ∈ a.parametrization '' Metric.ball (0 : Euclidean3) (3 / 4)
      refine ⟨z, ?_, hxeq.symm⟩
      simpa [Metric.mem_ball, dist_zero_right, hz_norm] using (show
        (1 / 2 : ℝ) < (3 / 4 : ℝ) by norm_num)
    have hqzx : q x = z := by
      dsimp [q]
      rw [← hxeq.symm]
      exact a.parametrization.left_inv hzsource
    have hρx : ρ x = (1 / 2 : ℝ) := by
      simp [ρ, hqzx, hz_norm]
    have hnx : n x = (s : Euclidean3) := by
      dsimp [n]
      rw [hρx, hqzx, show z = (1 / 2 : ℝ) • (s : Euclidean3) by rfl,
        smul_smul]
      norm_num
    rw [hfU_val x hxU, hρx, hnx]
    norm_num
  exact ⟨f, hf, hsurj, hfiber, hboundary⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
