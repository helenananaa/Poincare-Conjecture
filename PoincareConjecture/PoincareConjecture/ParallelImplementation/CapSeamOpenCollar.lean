import PoincareConjecture.ParallelImplementation.CappedSpaceTopology
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CapSeamOpenCollar
open Set PoincareConjecture.ParallelImplementation.CappedSpaceTopology
open scoped Topology
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Construct the actual collar across the ball-cap seam from a one-sided
collar of the original piece. The quotient and both coordinate formulas are
fixed, not an unspecified homeomorphic manifold or seam-chart certificate. -/
theorem exists_open_collar_across_actual_cap_seam
    {C : Type*} [TopologicalSpace C] [CompactSpace C] [T2Space C]
    (b : Sphere → C) (hb : Topology.IsEmbedding b)
    (k : Sphere × Ico (0 : ℝ) 1 → C) (hk : Topology.IsOpenEmbedding k)
    (hkzero : ∀ s : Sphere, k (s, ⟨0, by norm_num⟩) = b s) :
    ∃ e : Sphere × Ioo (-(1/2) : ℝ) (1/2) → CappedSpace b,
      Topology.IsOpenEmbedding e ∧
      (∀ (s : Sphere) (t : Ioo (-(1/2) : ℝ) (1/2)) (ht : 0 ≤ (t : ℝ)),
        e (s,t) = Quot.mk (capSeam b) (Sum.inl
          (k (s, ⟨(t : ℝ), ht, lt_trans t.2.2 (by norm_num)⟩)))) ∧
      (∀ (s : Sphere) (t : Ioo (-(1/2) : ℝ) (1/2)) (ht : (t : ℝ) ≤ 0),
        e (s,t) = Quot.mk (capSeam b) (Sum.inr
          (⟨(1 + (t : ℝ)) • (s : E3), by
            rw [Metric.mem_closedBall, dist_zero_right]
            have hs : ‖(s : E3)‖ = 1 := by
              simpa [Metric.mem_sphere, dist_zero_right] using s.2
            rw [norm_smul, Real.norm_eq_abs, hs, mul_one,
              abs_of_pos (by linarith [t.2.1])]
            linarith⟩ : Ball))) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let X := C ⊕ Ball
  let q : X → CappedSpace b := Quot.mk (capSeam b)
  let R : X → X → Prop := fun x y =>
    x = y ∨
      (∃ s : Sphere, x = Sum.inl (b s) ∧ y = Sum.inr (boundary s)) ∨
      (∃ s : Sphere, x = Sum.inr (boundary s) ∧ y = Sum.inl (b s))
  have hboundary_inj : Function.Injective (boundary : Sphere → Ball) := by
    intro s t h
    apply Subtype.ext
    exact congrArg (fun z : Ball => (z : E3)) h
  have hR_equiv : Equivalence R := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Or.inl rfl
    · intro x y hxy
      rcases hxy with hxy | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
      · exact Or.inl hxy.symm
      · exact Or.inr (Or.inr ⟨s, hy, hx⟩)
      · exact Or.inr (Or.inl ⟨s, hy, hx⟩)
    · intro x y z hxy hyz
      rcases hxy with hxy | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
      · cases hxy
        exact hyz
      · rcases hyz with hyz | ⟨t, hy', hz'⟩ | ⟨t, hy', hz'⟩
        · cases hyz
          exact Or.inr (Or.inl ⟨s, hx, hy⟩)
        · cases hy.symm.trans hy'
        · have hst' : boundary s = boundary t := Sum.inr.inj (hy.symm.trans hy')
          have hst : s = t := hboundary_inj hst'
          subst t
          exact Or.inl (hx.trans hz'.symm)
      · rcases hyz with hyz | ⟨t, hy', hz'⟩ | ⟨t, hy', hz'⟩
        · cases hyz
          exact Or.inr (Or.inr ⟨s, hx, hy⟩)
        · have hst' : b s = b t := Sum.inl.inj (hy.symm.trans hy')
          have hst : s = t := hb.injective hst'
          subst t
          exact Or.inl (hx.trans hz'.symm)
        · cases hy.symm.trans hy'
  have hseam_R : ∀ x y, capSeam b x y → R x y := by
    intro x y h
    rcases h with ⟨s, hx, hy⟩
    exact Or.inr (Or.inl ⟨s, hx, hy⟩)
  have hgen : ∀ x y, Relation.EqvGen (capSeam b) x y ↔ R x y := by
    intro x y
    constructor
    · intro h
      induction h with
      | rel a c hac => exact hseam_R a c hac
      | refl a => exact Or.inl rfl
      | symm a c hac ih => exact hR_equiv.symm ih
      | trans a c d hac hcd ihac ihcd => exact hR_equiv.trans ihac ihcd
    · intro h
      rcases h with h | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
      · cases h
        exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ ⟨s, hx, hy⟩
      · exact Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ ⟨s, hy, hx⟩)
  have hquot : ∀ x y, q x = q y ↔ R x y := by
    intro x y
    constructor
    · intro h
      exact (hgen x y).mp (Quot.eqvGen_exact h)
    · intro h
      exact Quot.eqvGen_sound ((hgen x y).mpr h)

  let D := Sphere × Ioo (-(1 / 2 : ℝ)) (1 / 2)
  let Collar := Sphere × Ico (0 : ℝ) 1
  let Plus : Set Collar := {z | (z.2 : ℝ) < 1 / 2}
  let PlusDom := {z : Collar // z ∈ Plus}
  let Minus := Sphere × Ioc (-(1 / 2 : ℝ)) 0
  let dPlus : PlusDom → D := fun z =>
    (z.1.1, ⟨z.1.2, by linarith [z.1.2.2.1], by
      have hz : (z.1.2 : ℝ) < 1 / 2 := by simpa [Plus] using z.2
      linarith [hz]⟩)
  let posParam : D → Collar := fun p =>
    (p.1, ⟨max 0 (p.2 : ℝ), le_max_left _ _,
      max_lt_iff.mpr ⟨by norm_num, lt_trans p.2.2.2 (by norm_num)⟩⟩)
  let α : D → ℝ := fun p => min 1 (1 + (p.2 : ℝ))
  let negVec : D → E3 := fun p => α p • (p.1 : E3)
  have hneg_ball : ∀ p : D, negVec p ∈ Ball := by
    intro p
    rw [Metric.mem_closedBall, dist_zero_right]
    have hpα : 0 ≤ α p := by
      dsimp [α]
      exact le_min (by norm_num) (by linarith [p.2.2.1])
    have hs : ‖(p.1 : E3)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using p.1.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpα, hs]
    simpa [α] using (min_le_left (1 : ℝ) (1 + (p.2 : ℝ)))
  let negParam : D → Ball := fun p => ⟨negVec p, hneg_ball p⟩
  let pos : D → CappedSpace b := fun p => q (Sum.inl (k (posParam p)))
  let neg : D → CappedSpace b := fun p => q (Sum.inr (negParam p))
  let e : D → CappedSpace b := fun p => if (p.2 : ℝ) ≤ 0 then neg p else pos p
  have hposParam_cont : Continuous posParam := by
    have hmax_cont : Continuous (fun p : D => max 0 (p.2 : ℝ)) :=
      continuous_const.max (continuous_subtype_val.comp continuous_snd)
    have hmax_subtype : Continuous (fun p : D =>
        (⟨max 0 (p.2 : ℝ), le_max_left _ _,
          max_lt_iff.mpr ⟨by norm_num, lt_trans p.2.2.2 (by norm_num)⟩⟩ : Ico (0 : ℝ) 1)) :=
      hmax_cont.subtype_mk (fun p => ⟨le_max_left _ _,
        max_lt_iff.mpr ⟨by norm_num, lt_trans p.2.2.2 (by norm_num)⟩⟩)
    change Continuous (fun p : D =>
      (p.1, (⟨max 0 (p.2 : ℝ), le_max_left _ _,
        max_lt_iff.mpr ⟨by norm_num, lt_trans p.2.2.2 (by norm_num)⟩⟩ : Ico (0 : ℝ) 1))
    )
    exact continuous_fst.prodMk hmax_subtype
  have hα_cont : Continuous α := by
    change Continuous (fun p : D => min 1 (1 + (p.2 : ℝ)))
    exact continuous_const.min
      (continuous_const.add (continuous_subtype_val.comp continuous_snd))
  have hnegVec_cont : Continuous negVec := by
    dsimp [negVec]
    exact hα_cont.smul (continuous_subtype_val.comp continuous_fst)
  have hnegParam_cont : Continuous negParam := hnegVec_cont.subtype_mk hneg_ball
  have hpos_cont : Continuous pos := by
    dsimp [pos]
    exact continuous_quot_mk.comp (continuous_inl.comp
      (hk.continuous.comp hposParam_cont))
  have hneg_cont : Continuous neg := by
    dsimp [neg]
    exact continuous_quot_mk.comp (continuous_inr.comp hnegParam_cont)
  have hneg_eq_pos_at_zero : ∀ p : D, (p.2 : ℝ) = 0 → neg p = pos p := by
    intro p hp
    have hparam : posParam p = (p.1, (⟨0, by norm_num, by norm_num⟩ : Ico (0 : ℝ) 1)) := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp [posParam, hp]
    have hball : negParam p = boundary p.1 := by
      apply Subtype.ext
      simp [negParam, negVec, α, boundary, hp]
    have hpos_neg : pos p = neg p := by
      change q (Sum.inl (k (posParam p))) = q (Sum.inr (negParam p))
      rw [hparam, hkzero p.1, hball]
      apply Quot.sound
      exact ⟨p.1, rfl, rfl⟩
    exact hpos_neg.symm
  have hfrontier_zero : ∀ p : D, p ∈ frontier {x : D | (x.2 : ℝ) ≤ 0} →
      (p.2 : ℝ) = 0 := by
    intro p hp
    have hcont : Continuous (fun x : D => (x.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hclosed : IsClosed {x : D | (x.2 : ℝ) ≤ 0} := isClosed_le hcont continuous_const
    have hnonpos : (p.2 : ℝ) ≤ 0 := by
      have hpS : p ∈ {x : D | (x.2 : ℝ) ≤ 0} := hclosed.closure_eq ▸ hp.1
      exact hpS
    have hnotneg : ¬ (p.2 : ℝ) < 0 := by
      intro hn
      have hopen : IsOpen {x : D | (x.2 : ℝ) < 0} :=
        isOpen_lt hcont continuous_const
      have hsubset : {x : D | (x.2 : ℝ) < 0} ⊆ {x : D | (x.2 : ℝ) ≤ 0} :=
        fun x hx => by change (x.2 : ℝ) < 0 at hx; exact le_of_lt hx
      have hInt : p ∈ interior {x : D | (x.2 : ℝ) < 0} := by
        rw [hopen.interior_eq]
        exact hn
      have hint : p ∈ interior {x : D | (x.2 : ℝ) ≤ 0} := interior_mono hsubset hInt
      exact hp.2 hint
    exact le_antisymm hnonpos (le_of_not_gt hnotneg)
  have he_cont : Continuous e := by
    apply continuous_if
    · intro p hp
      have hp0 := hfrontier_zero p hp
      simp [e, hp0, hneg_eq_pos_at_zero p hp0]
    · exact hneg_cont.continuousOn.mono (subset_univ _)
    · exact hpos_cont.continuousOn.mono (subset_univ _)

  have he_nonneg : ∀ (s : Sphere) (t : Ioo (-(1 / 2 : ℝ)) (1 / 2))
      (ht : 0 ≤ (t : ℝ)), e (s,t) = q (Sum.inl
        (k (s, ⟨(t : ℝ), ht, lt_trans t.2.2 (by norm_num)⟩))) := by
    intro s t ht
    by_cases ht0 : (t : ℝ) = 0
    · have h := hneg_eq_pos_at_zero (s,t) ht0
      change (if (t : ℝ) ≤ 0 then neg (s,t) else pos (s,t)) = _
      rw [if_pos (le_of_eq ht0), h]
      change q (Sum.inl (k (posParam (s,t)))) = _
      have hparam : posParam (s,t) = (s, (⟨0, by norm_num, by norm_num⟩ : Ico (0 : ℝ) 1)) := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [posParam, ht0]
      rw [hparam]
      simp [ht0]
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne ht (Ne.symm ht0)
      simp only [e, if_neg (not_le_of_gt htpos)]
      change q (Sum.inl (k (posParam (s,t)))) = _
      have hparam : posParam (s,t) = (s, (⟨(t : ℝ), ht,
          lt_trans t.2.2 (by norm_num)⟩ : Ico (0 : ℝ) 1)) := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [posParam, max_eq_right ht]
      rw [hparam]
  have he_nonpos : ∀ (s : Sphere) (t : Ioo (-(1 / 2 : ℝ)) (1 / 2))
      (ht : (t : ℝ) ≤ 0), e (s,t) = q (Sum.inr
        (⟨(1 + (t : ℝ)) • (s : E3), by
          rw [Metric.mem_closedBall, dist_zero_right]
          have hs : ‖(s : E3)‖ = 1 := by
            simpa [Metric.mem_sphere, dist_zero_right] using s.2
          rw [norm_smul, Real.norm_eq_abs, hs, mul_one,
            abs_of_pos (by linarith [t.2.1])]
          linarith⟩ : Ball)) := by
    intro s t ht
    simp only [e, if_pos ht]
    change q (Sum.inr (negParam (s,t))) = _
    apply congrArg (fun z : Ball => q (Sum.inr z))
    apply Subtype.ext
    simp [negParam, negVec, α, min_eq_right (by linarith : 1 + (t : ℝ) ≤ 1)]

  let radialVec : Minus → E3 := fun z => (1 + (z.2 : ℝ)) • (z.1 : E3)
  have hradVec_cont : Continuous radialVec := by
    dsimp [radialVec]
    exact (continuous_const.add (continuous_subtype_val.comp continuous_snd)).smul
      (continuous_subtype_val.comp continuous_fst)
  have hrad_ball : ∀ z : Minus, radialVec z ∈ Ball := by
    intro z
    rw [Metric.mem_closedBall, dist_zero_right]
    have htpos : 0 < 1 + (z.2 : ℝ) := by linarith [z.2.2.1]
    have hs : ‖(z.1 : E3)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using z.1.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, hs, mul_one]
    linarith [z.2.2.2]
  let radial : Minus → Ball := fun z => ⟨radialVec z, hrad_ball z⟩
  have hrad_cont : Continuous radial := hradVec_cont.subtype_mk hrad_ball
  have hrad_norm : ∀ z : Minus, ‖(radial z : E3)‖ = 1 + (z.2 : ℝ) := by
    intro z
    dsimp [radial, radialVec]
    have htpos : 0 < 1 + (z.2 : ℝ) := by linarith [z.2.2.1]
    have hs : ‖(z.1 : E3)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using z.1.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, hs, mul_one]
  let Shell : Set Ball := {x | (1 / 2 : ℝ) < ‖(x : E3)‖}
  let ShellPoint := {x : Ball // x ∈ Shell}
  have hball_norm_le : ∀ x : Ball, ‖(x : E3)‖ ≤ 1 := by
    intro x
    have hmem : dist (x : E3) (0 : E3) ≤ 1 := x.2
    simpa only [dist_zero_right] using hmem
  have hShell_open : IsOpen Shell := by
    dsimp [Shell]
    exact isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
  have hShell_lower : ∀ x : ShellPoint, (1 / 2 : ℝ) < ‖(x.1 : E3)‖ := by
    intro x
    simpa [Shell] using x.2
  have hrad_shell : ∀ z : Minus, radial z ∈ Shell := by
    intro z
    change (1 / 2 : ℝ) < ‖(radial z : E3)‖
    rw [hrad_norm]
    linarith [z.2.2.1]
  let radialShell : Minus → ShellPoint := fun z => ⟨radial z, hrad_shell z⟩
  let unitVec : ShellPoint → E3 := fun x => ‖(x.1 : E3)‖⁻¹ • (x.1 : E3)
  have hunit_norm : ∀ x : ShellPoint, ‖unitVec x‖ = 1 := by
    intro x
    have hxpos : 0 < ‖(x.1 : E3)‖ := lt_trans (by norm_num) (hShell_lower x)
    dsimp [unitVec]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hxpos)]
    exact inv_mul_cancel₀ hxpos.ne'
  let radialCoord : ShellPoint → Minus := fun x =>
    (⟨unitVec x, by
      rw [Metric.mem_sphere, dist_zero_right]
      exact hunit_norm x⟩,
      ⟨‖(x.1 : E3)‖ - 1, by linarith [hShell_lower x], by
        linarith [hball_norm_le x.1]⟩)
  have hcoord_cont : Continuous radialCoord := by
    have hxcont : Continuous (fun x : ShellPoint => (x.1 : E3)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hncont : Continuous (fun x : ShellPoint => ‖(x.1 : E3)‖) :=
      continuous_norm.comp hxcont
    have hinvcont : Continuous (fun x : ShellPoint => ‖(x.1 : E3)‖⁻¹) :=
      hncont.inv₀ (fun x => ne_of_gt (lt_trans (by norm_num) (hShell_lower x)))
    have hdir : Continuous unitVec := by
      dsimp [unitVec]
      exact hinvcont.smul hxcont
    have hdirSphere : Continuous (fun x : ShellPoint =>
        (⟨unitVec x, by rw [Metric.mem_sphere, dist_zero_right]; exact hunit_norm x⟩ : Sphere)) :=
      hdir.subtype_mk (fun x => by
        rw [Metric.mem_sphere, dist_zero_right]
        exact hunit_norm x)
    have hradcoord : Continuous (fun x : ShellPoint =>
        ‖(x.1 : E3)‖ - 1) := hncont.sub continuous_const
    have hradSubtype : Continuous (fun x : ShellPoint =>
        (⟨‖(x.1 : E3)‖ - 1, by linarith [hShell_lower x], by
          linarith [hball_norm_le x.1]⟩ : Ioc (-(1 / 2 : ℝ)) 0)) :=
      hradcoord.subtype_mk (fun x => by
        constructor
        · linarith [hShell_lower x]
        · linarith [hball_norm_le x.1])
    change Continuous (fun x : ShellPoint =>
      ((⟨unitVec x, by
          rw [Metric.mem_sphere, dist_zero_right]
          exact hunit_norm x⟩ : Sphere),
       (⟨‖(x.1 : E3)‖ - 1, by linarith [hShell_lower x], by
          linarith [hball_norm_le x.1]⟩ : Ioc (-(1 / 2 : ℝ)) 0)))
    exact hdirSphere.prodMk hradSubtype
  have hcoord_rad : ∀ z : Minus, radialCoord (radialShell z) = z := by
    intro z
    apply Prod.ext
    · apply Subtype.ext
      change ‖(radial z : E3)‖⁻¹ • (radial z : E3) = (z.1 : E3)
      rw [hrad_norm z]
      change (1 + (z.2 : ℝ))⁻¹ •
        ((1 + (z.2 : ℝ)) • (z.1 : E3)) = (z.1 : E3)
      have hr : 1 + (z.2 : ℝ) ≠ 0 := ne_of_gt (by linarith [z.2.2.1])
      rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
    · apply Subtype.ext
      change ‖(radial z : E3)‖ - 1 = (z.2 : ℝ)
      rw [hrad_norm z]
      ring
  have hrad_coord : ∀ x : ShellPoint, radialShell (radialCoord x) = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change (1 + (‖(x.1 : E3)‖ - 1)) • unitVec x = (x.1 : E3)
    rw [show 1 + (‖(x.1 : E3)‖ - 1) = ‖(x.1 : E3)‖ by ring]
    have hr : ‖(x.1 : E3)‖ ≠ 0 := ne_of_gt (lt_trans (by norm_num) (hShell_lower x))
    dsimp [unitVec]
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
  have hrad_openMap : IsOpenMap radial := by
    intro U hU
    have himage : radial '' U = (Subtype.val : ShellPoint → Ball) '' (radialCoord ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨radialShell z, ?_, rfl⟩
        change radialCoord (radialShell z) ∈ U
        rw [hcoord_rad]
        exact hz
      · rintro ⟨x, hx, hy⟩
        refine ⟨radialCoord x, hx, ?_⟩
        have hh := congrArg (Subtype.val : ShellPoint → Ball) (hrad_coord x)
        exact hh.trans hy
    rw [himage]
    exact hShell_open.isOpenEmbedding_subtypeVal.isOpenMap _
      (hcoord_cont.isOpen_preimage _ hU)
  have hrad_inj : Function.Injective radial := by
    intro z w hzw
    have hsw : radialShell z = radialShell w := Subtype.ext hzw
    have h := congrArg radialCoord hsw
    simpa [hcoord_rad] using h
  have hrad_embedding : Topology.IsOpenEmbedding radial :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hrad_cont hrad_inj hrad_openMap

  have hpos_inj : ∀ p r : D, 0 < (p.2 : ℝ) → 0 < (r.2 : ℝ) →
      pos p = pos r → p = r := by
    intro p r hp hr hpr
    have hR := (hquot (Sum.inl (k (posParam p))) (Sum.inl (k (posParam r)))).mp hpr
    rcases hR with heq | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
    · have hparam := hk.injective (Sum.inl.inj heq)
      change (p.1, p.2) = (r.1, r.2)
      apply Prod.ext
      · simpa [posParam] using congrArg Prod.fst hparam
      · apply Subtype.ext
        have ht := congrArg (fun z : Collar => (z.2 : ℝ)) hparam
        simpa [posParam, max_eq_right (le_of_lt hp), max_eq_right (le_of_lt hr)] using ht
    · cases hy
    · cases hx

  let toMinus : ∀ p : D, (p.2 : ℝ) ≤ 0 → Minus := fun p hp =>
    (p.1, ⟨(p.2 : ℝ), by linarith [p.2.2.1], hp⟩)
  have hneg_rad : ∀ (p : D) (hp : (p.2 : ℝ) ≤ 0),
      negParam p = radial (toMinus p hp) := by
    intro p hp
    apply Subtype.ext
    simp [negParam, negVec, α, radial, radialVec, toMinus,
      min_eq_right (show 1 + (p.2 : ℝ) ≤ 1 by linarith)]
  have hneg_inj : ∀ p r : D, (hp : (p.2 : ℝ) ≤ 0) → (hr : (r.2 : ℝ) ≤ 0) →
      neg p = neg r → p = r := by
    intro p r hp hr hpr
    have hR := (hquot (Sum.inr (negParam p)) (Sum.inr (negParam r))).mp hpr
    have hball : negParam p = negParam r := by
      rcases hR with heq | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
      · exact Sum.inr.inj heq
      · cases hx
      · cases hy
    have hradEq : radial (toMinus p hp) = radial (toMinus r hr) := by
      rw [← hneg_rad p hp, ← hneg_rad r hr]
      exact hball
    have hcoordEq := hrad_embedding.injective hradEq
    change (p.1, p.2) = (r.1, r.2)
    apply Prod.ext
    · simpa [toMinus] using congrArg (fun z : Minus => z.1) hcoordEq
    · apply Subtype.ext
      simpa [toMinus] using congrArg (fun z : Minus => (z.2 : ℝ)) hcoordEq
  have hcross_neg_pos : ∀ p r : D, (hp : (p.2 : ℝ) ≤ 0) →
      (hr : 0 < (r.2 : ℝ)) → e p = e r → False := by
    intro p r hp hr hpr
    have hpr' : q (Sum.inr (negParam p)) = q (Sum.inl (k (posParam r))) := by
      simpa [e, neg, pos, hp, not_le_of_gt hr] using hpr
    have hR := (hquot (Sum.inr (negParam p)) (Sum.inl (k (posParam r)))).mp hpr'
    rcases hR with heq | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
    · cases heq
    · cases hx
    · have hrad : negParam p = boundary s := Sum.inr.inj hx
      have hkval : k (posParam r) = b s := Sum.inl.inj hy
      have hnormS : ‖(boundary s : E3)‖ = 1 := by
        have hs : ‖(s : E3)‖ = 1 := by
          simpa [Metric.mem_sphere, dist_zero_right] using s.2
        simpa [boundary] using hs
      have hnorm := congrArg (fun z : Ball => ‖(z : E3)‖) hrad
      rw [hneg_rad p hp, hrad_norm, hnormS] at hnorm
      have htime : (p.2 : ℝ) = 0 := by
        have ht : ((toMinus p hp).2 : ℝ) = 0 := by linarith [hnorm]
        simpa [toMinus] using ht
      have hzero : k (s, (⟨0, by norm_num, by norm_num⟩ : Ico (0 : ℝ) 1)) = b s := hkzero s
      have hparam := hk.injective (hkval.trans hzero.symm)
      have hrt : (r.2 : ℝ) = 0 := by
        have hv := congrArg (fun z : Collar => (z.2 : ℝ)) hparam
        simpa [posParam, max_eq_right (le_of_lt hr)] using hv
      linarith
  have he_inj : Function.Injective e := by
    intro p r hpr
    by_cases hp : (p.2 : ℝ) ≤ 0
    · by_cases hr : (r.2 : ℝ) ≤ 0
      · exact hneg_inj p r hp hr (by simpa [e, hp, hr] using hpr)
      · exact False.elim (hcross_neg_pos p r hp (lt_of_not_ge hr) hpr)
    · by_cases hr : (r.2 : ℝ) ≤ 0
      · exact False.elim (hcross_neg_pos r p hr (lt_of_not_ge hp) hpr.symm)
      · exact hpos_inj p r (lt_of_not_ge hp) (lt_of_not_ge hr)
          (by simpa [e, hp, hr] using hpr)

  have hPlus_open : IsOpen Plus := by
    dsimp [Plus]
    exact isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
  have hplusChart : Topology.IsOpenEmbedding (fun z : PlusDom => k z.1) := by
    change Topology.IsOpenEmbedding (k ∘ (Subtype.val : PlusDom → Collar))
    exact hk.comp hPlus_open.isOpenEmbedding_subtypeVal
  have hdPlus_cont : Continuous dPlus := by
    have htime : Continuous (fun z : PlusDom => (z.1.2 : ℝ)) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
    have htimeD : Continuous (fun z : PlusDom =>
        (⟨(z.1.2 : ℝ), by linarith [z.1.2.2.1], by
          have hz : (z.1.2 : ℝ) < 1 / 2 := by simpa [Plus] using z.2
          linarith [hz]⟩ : Ioo (-(1 / 2 : ℝ)) (1 / 2))) :=
      htime.subtype_mk (fun z => ⟨by linarith [z.1.2.2.1], by
        have hz : (z.1.2 : ℝ) < 1 / 2 := by simpa [Plus] using z.2
        exact hz⟩)
    change Continuous (fun z : PlusDom =>
      (z.1.1, (⟨(z.1.2 : ℝ), by linarith [z.1.2.2.1], by
        have hz : (z.1.2 : ℝ) < 1 / 2 := by simpa [Plus] using z.2
        linarith [hz]⟩ : Ioo (-(1 / 2 : ℝ)) (1 / 2))))
    exact (continuous_fst.comp continuous_subtype_val).prodMk htimeD
  let dMinus : Minus → D := fun z =>
    (z.1, ⟨(z.2 : ℝ), z.2.2.1, lt_of_le_of_lt z.2.2.2 (by norm_num)⟩)
  have hdMinus_cont : Continuous dMinus := by
    have htime : Continuous (fun z : Minus => (z.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have htimeD : Continuous (fun z : Minus =>
        (⟨(z.2 : ℝ), z.2.2.1, lt_of_le_of_lt z.2.2.2 (by norm_num)⟩ : Ioo (-(1 / 2 : ℝ)) (1 / 2))) :=
      htime.subtype_mk (fun z => ⟨z.2.2.1,
        lt_of_le_of_lt z.2.2.2 (by norm_num)⟩)
    change Continuous (fun z : Minus =>
      (z.1, (⟨(z.2 : ℝ), z.2.2.1,
        lt_of_le_of_lt z.2.2.2 (by norm_num)⟩ : Ioo (-(1 / 2 : ℝ)) (1 / 2))))
    exact continuous_fst.prodMk htimeD
  have hdMinus_toMinus : ∀ (p : D) (hp : (p.2 : ℝ) ≤ 0), dMinus (toMinus p hp) = p := by
    intro p hp
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  let toPlus : ∀ (p : D) (hp : 0 ≤ (p.2 : ℝ)), PlusDom := fun p hp =>
    ⟨posParam p, by
      have ht : ((posParam p).2 : ℝ) < 1 / 2 := by
        dsimp [posParam]
        exact max_lt_iff.mpr ⟨by norm_num, p.2.2.2⟩
      simpa [Plus] using ht⟩
  have hdPlus_toPlus : ∀ (p : D) (hp : 0 ≤ (p.2 : ℝ)), dPlus (toPlus p hp) = p := by
    intro p hp
    apply Prod.ext
    · simp [dPlus, toPlus, posParam]
    · apply Subtype.ext
      simp [dPlus, toPlus, posParam, max_eq_right hp]

  let plusZero : Sphere → PlusDom := fun s =>
    ⟨(s, (⟨0, by norm_num, by norm_num⟩ : Ico (0 : ℝ) 1)), by
      simp [Plus]⟩
  let minusZero : Sphere → Minus := fun s =>
    (s, (⟨0, by norm_num, by norm_num⟩ : Ioc (-(1 / 2 : ℝ)) 0))
  let atZero : Sphere → D := fun s =>
    (s, (⟨0, by norm_num, by norm_num⟩ : Ioo (-(1 / 2 : ℝ)) (1 / 2)))
  have hdPlus_zero : ∀ s : Sphere, dPlus (plusZero s) = atZero s := by
    intro s
    apply Prod.ext <;> simp [dPlus, plusZero, atZero]
  have hdMinus_zero : ∀ s : Sphere, dMinus (minusZero s) = atZero s := by
    intro s
    apply Prod.ext <;> simp [dMinus, minusZero, atZero]
  have hradial_zero : ∀ s : Sphere, radial (minusZero s) = boundary s := by
    intro s
    apply Subtype.ext
    simp [radial, radialVec, minusZero, boundary]
  have he_openMap : IsOpenMap e := by
    intro U hU
    let Uplus : Set PlusDom := dPlus ⁻¹' U
    let Uminus : Set Minus := dMinus ⁻¹' U
    let Vplus : Set C := (fun z : PlusDom => k z.1) '' Uplus
    let Vminus : Set Ball := radial '' Uminus
    let W : Set X := Sum.inl '' Vplus ∪ Sum.inr '' Vminus
    have hUplus_open : IsOpen Uplus := hdPlus_cont.isOpen_preimage _ hU
    have hUminus_open : IsOpen Uminus := hdMinus_cont.isOpen_preimage _ hU
    have hVplus_open : IsOpen Vplus := hplusChart.isOpenMap _ hUplus_open
    have hVminus_open : IsOpen Vminus := hrad_embedding.isOpenMap _ hUminus_open
    have hW_open : IsOpen W :=
      (isOpenMap_inl _ hVplus_open).union (isOpenMap_inr _ hVminus_open)
    have hW_sat : q ⁻¹' (q '' W) = W := by
      ext x
      constructor
      · rintro ⟨y, hyW, hqyx⟩
        rcases hyW with hyP | hyN
        · rcases hyP with ⟨c, hc, rfl⟩
          rcases hc with ⟨z, hz, rfl⟩
          have hR := (hquot (Sum.inl (k z.1)) x).mp hqyx
          rcases hR with heq | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
          · rw [← heq]
            exact Or.inl ⟨k z.1, ⟨z, hz, rfl⟩, rfl⟩
          · have hparam := hk.injective ((Sum.inl.inj hx).trans (hkzero s).symm)
            have hd : dPlus z = atZero s := by
              apply Prod.ext
              · simpa [dPlus, atZero] using congrArg Prod.fst hparam
              · apply Subtype.ext
                simpa [dPlus, atZero] using
                  congrArg (fun c : Collar => (c.2 : ℝ)) hparam
            have hUzero : atZero s ∈ U := by rw [← hd]; exact hz
            have hmU : minusZero s ∈ Uminus := by
              change dMinus (minusZero s) ∈ U
              rw [hdMinus_zero]
              exact hUzero
            have hradW : boundary s ∈ Vminus := by
              exact ⟨minusZero s, hmU, hradial_zero s⟩
            rw [hy]
            exact Or.inr ⟨boundary s, hradW, rfl⟩
          · cases hx
        · rcases hyN with ⟨v, hv, rfl⟩
          rcases hv with ⟨m, hm, rfl⟩
          have hR := (hquot (Sum.inr (radial m)) x).mp hqyx
          rcases hR with heq | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
          · rw [← heq]
            exact Or.inr ⟨radial m, ⟨m, hm, rfl⟩, rfl⟩
          · cases hx
          · have hrad : radial m = boundary s := Sum.inr.inj hx
            have hmzero : m = minusZero s := hrad_inj (by rw [hradial_zero]; exact hrad)
            have hUm : dMinus m ∈ U := hm
            have hUzero : atZero s ∈ U := by
              rw [← hdMinus_zero s, ← hmzero]
              exact hUm
            have hpU : plusZero s ∈ Uplus := by
              change dPlus (plusZero s) ∈ U
              rw [hdPlus_zero]
              exact hUzero
            have hposW : b s ∈ Vplus := by
              exact ⟨plusZero s, hpU, hkzero s⟩
            rw [hy]
            exact Or.inl ⟨b s, hposW, rfl⟩
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hqmap : Topology.IsQuotientMap q := isQuotientMap_quot_mk
    have hqW_open : IsOpen (q '' W) := by
      apply hqmap.isOpen_preimage.mp
      rw [hW_sat]
      exact hW_open
    have hImage : e '' U = q '' W := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        by_cases ht : (p.2 : ℝ) ≤ 0
        · have hmU : toMinus p ht ∈ Uminus := by
            change dMinus (toMinus p ht) ∈ U
            rw [hdMinus_toMinus p ht]
            exact hp
          have hnegout : e p = q (Sum.inr (radial (toMinus p ht))) := by
            calc
              e p = neg p := by simp [e, ht]
              _ = q (Sum.inr (negParam p)) := rfl
              _ = q (Sum.inr (radial (toMinus p ht))) :=
                congrArg (fun z : Ball => q (Sum.inr z)) (hneg_rad p ht)
          rw [hnegout]
          refine ⟨Sum.inr (radial (toMinus p ht)), ?_, rfl⟩
          exact Or.inr ⟨radial (toMinus p ht), ⟨toMinus p ht, hmU, rfl⟩, rfl⟩
        · have ht : 0 < (p.2 : ℝ) := lt_of_not_ge ht
          have hpU : toPlus p (le_of_lt ht) ∈ Uplus := by
            change dPlus (toPlus p (le_of_lt ht)) ∈ U
            rw [hdPlus_toPlus p (le_of_lt ht)]
            exact hp
          have hposout : e p = q (Sum.inl (k (toPlus p (le_of_lt ht)).1)) := by
            simp [e, pos, toPlus, not_le_of_gt ht]
          rw [hposout]
          refine ⟨Sum.inl (k (toPlus p (le_of_lt ht)).1), ?_, rfl⟩
          exact Or.inl ⟨k (toPlus p (le_of_lt ht)).1,
            ⟨toPlus p (le_of_lt ht), hpU, rfl⟩, rfl⟩
      · rintro ⟨z, hzW, hzy⟩
        rcases hzW with hzP | hzN
        · rcases hzP with ⟨c, hc, rfl⟩
          rcases hc with ⟨z, hz, rfl⟩
          have hp : dPlus z ∈ U := hz
          have ht : 0 ≤ ((dPlus z).2 : ℝ) := by
            simp [dPlus]
            exact z.1.2.2.1
          have hFormula := he_nonneg (dPlus z).1 (dPlus z).2 ht
          have hparam : posParam (dPlus z) = z.1 := by
            apply Prod.ext
            · rfl
            · apply Subtype.ext
              simp [posParam, dPlus, max_eq_right ht]
          have hpU := hp
          rw [← hzy]
          refine ⟨dPlus z, hpU, ?_⟩
          simpa [pos, hparam] using hFormula
        · rcases hzN with ⟨v, hv, rfl⟩
          rcases hv with ⟨m, hm, rfl⟩
          have hp : dMinus m ∈ U := hm
          have ht : ((dMinus m).2 : ℝ) ≤ 0 := by
            simp [dMinus]
            exact m.2.2.2
          have hFormula := he_nonpos (dMinus m).1 (dMinus m).2 ht
          rw [← hzy]
          refine ⟨dMinus m, hp, ?_⟩
          simpa [dMinus, radial, radialVec] using hFormula
    rw [hImage]
    exact hqW_open
  have he_embedding : Topology.IsOpenEmbedding e :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap he_cont he_inj he_openMap
  exact ⟨e, he_embedding, he_nonneg, he_nonpos⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CapSeamOpenCollar
