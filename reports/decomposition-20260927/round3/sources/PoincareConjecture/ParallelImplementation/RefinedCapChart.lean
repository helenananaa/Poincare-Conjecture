import PoincareConjecture.ProofContract.Refinement20260927.Cap
import PoincareConjecture.ParallelImplementation.CapSeamOpenCollar
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedCapChart
open PoincareConjecture.ProofContract.Refinement20260927
theorem cap_chart : CapChartStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro c
  letI : CompactSpace c.carrier := c.compact
  letI : T2Space c.carrier := c.hausdorff
  let E3 := EuclideanSpace ℝ (Fin 3)
  let Ball := Metric.closedBall (0 : E3) 1
  let Ball3 := Metric.ball (0 : E3) 3
  let Sphere2 := Metric.sphere (0 : E3) 1
  let CappedSpace := fun {C : Type u} (b : Sphere2 → C) =>
    PoincareConjecture.ParallelImplementation.CappedSpaceTopology.CappedSpace b
  let boundary := PoincareConjecture.ParallelImplementation.CappedSpaceTopology.boundary
  let capSeam := fun {C : Type u} (b : Sphere2 → C) (x y : C ⊕ Ball) =>
    PoincareConjecture.ParallelImplementation.CappedSpaceTopology.capSeam b x y
  let Inner := {x : Ball3 // ‖(x : E3)‖ < 1}
  let Shell := {x : Ball3 // (1 / 2 : ℝ) < ‖(x : E3)‖}
  let D := Sphere2 × Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
  let rho : ℝ → ℝ := fun r => min (r - 1) ((r - 1) / 4)
  let sigma : ℝ → ℝ := fun t => max (1 + t) (1 + 4 * t)

  obtain ⟨seamChart, hseamChart, hseamPos, hseamNeg⟩ :=
    PoincareConjecture.ParallelImplementation.CapSeamOpenCollar.exists_open_collar_across_actual_cap_seam
      c.boundaryMap c.boundaryEmbedding c.collar c.collarEmbedding c.collarZero

  have htop := PoincareConjecture.ParallelImplementation.CappedSpaceTopology.actual_cap_quotient_topology
    c.boundaryMap c.boundaryEmbedding
  have hcapEmb : Topology.IsOpenEmbedding (capInterior c) := by
    simpa [capInterior] using htop.2.2.2

  let coord : Shell → D := fun x =>
    (⟨‖(x : E3)‖⁻¹ • (x : E3), by
        have hxpos : 0 < ‖(x : E3)‖ := lt_trans (by norm_num) x.2
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hxpos)]
        exact inv_mul_cancel₀ hxpos.ne'⟩,
      ⟨rho ‖(x : E3)‖, by
        dsimp [rho]
        by_cases hh : ‖(x : E3)‖ - 1 ≤ (‖(x : E3)‖ - 1) / 4
        · rw [min_eq_left hh]
          linarith [x.2]
        · rw [min_eq_right (le_of_not_ge hh)]
          linarith [x.2],
        by
          dsimp [rho]
          have hx3 : ‖(x.1 : E3)‖ < 3 := by
            have hxDist : dist (x.1 : E3) (0 : E3) < 3 := x.1.2
            simpa only [dist_zero_right] using hxDist
          exact lt_of_le_of_lt (min_le_right _ _) (by linarith [hx3])⟩)

  have hsigmaPos (p : D) : 0 < sigma (p.2 : ℝ) := by
    dsimp [sigma]
    exact lt_of_lt_of_le (by linarith [p.2.2.1]) (le_max_left _ _)
  have hsigmaLt (p : D) : sigma (p.2 : ℝ) < 3 := by
    dsimp [sigma]
    exact max_lt_iff.mpr ⟨by linarith [p.2.2.2], by linarith [p.2.2.2]⟩
  have hsigmaGt (p : D) : (1 / 2 : ℝ) < sigma (p.2 : ℝ) := by
    dsimp [sigma]
    exact lt_of_lt_of_le (by linarith [p.2.2.1]) (le_max_left _ _)

  let uncoord : D → Shell := fun p =>
    ⟨⟨sigma (p.2 : ℝ) • (p.1 : E3), by
        have hs : ‖(p.1 : E3)‖ = 1 := by
          simpa [Metric.mem_sphere, dist_zero_right] using p.1.2
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (hsigmaPos p), hs]
        simpa [hs] using hsigmaLt p⟩,
      by
        have hs : ‖(p.1 : E3)‖ = 1 := by
          simpa [Metric.mem_sphere, dist_zero_right] using p.1.2
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hsigmaPos p), hs]
        simpa [hs] using hsigmaGt p⟩

  have hrho_sigma : ∀ r : ℝ, (1 / 2 : ℝ) < r → r < 3 → sigma (rho r) = r := by
    intro r hr0 hr3
    by_cases hr : r ≤ 1
    · have hmin : min (r - 1) ((r - 1) / 4) = r - 1 := by
        apply min_eq_left
        linarith
      have hmax : max (1 + (r - 1)) (1 + 4 * (r - 1)) = r := by
        rw [show 1 + (r - 1) = r by ring,
          show 1 + 4 * (r - 1) = 4 * r - 3 by ring,
          max_eq_left (by linarith : 4 * r - 3 ≤ r)]
      simp only [sigma, rho, hmin, hmax]
    · have hr1 : 1 < r := lt_of_not_ge hr
      have hmin : min (r - 1) ((r - 1) / 4) = (r - 1) / 4 := by
        apply min_eq_right
        linarith
      have hmax : max (1 + ((r - 1) / 4))
          (1 + 4 * ((r - 1) / 4)) = r := by
        rw [show 1 + 4 * ((r - 1) / 4) = r by ring,
          max_eq_right (by linarith : 1 + ((r - 1) / 4) ≤ r)]
      simp only [sigma, rho, hmin, hmax]

  have hrho_sigma' : ∀ t : ℝ, (-(1 / 2) : ℝ) < t → t < 1 / 2 → rho (sigma t) = t := by
    intro t ht0 ht1
    by_cases ht : t ≤ 0
    · have hmax : max (1 + t) (1 + 4 * t) = 1 + t := by
        apply max_eq_left
        linarith
      have hmin : min ((1 + t) - 1) (((1 + t) - 1) / 4) = t := by
        rw [show (1 + t) - 1 = t by ring]
        apply min_eq_left
        linarith
      simp only [rho, sigma, hmax, hmin]
    · have htpos : 0 < t := lt_of_not_ge ht
      have hmax : max (1 + t) (1 + 4 * t) = 1 + 4 * t := by
        apply max_eq_right
        linarith
      have hmin : min ((1 + 4 * t) - 1) (((1 + 4 * t) - 1) / 4) = t := by
        rw [show (1 + 4 * t) - 1 = 4 * t by ring,
          show (4 * t) / 4 = t by ring]
        apply min_eq_right
        linarith
      simp only [rho, sigma, hmax, hmin]

  have hcoord_cont : Continuous coord := by
    have hx : Continuous (fun x : Shell => (x : E3)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hr : Continuous (fun x : Shell => ‖(x : E3)‖) :=
      continuous_norm.comp hx
    have hinv : Continuous (fun x : Shell => ‖(x : E3)‖⁻¹) :=
      hr.inv₀ (fun x => ne_of_gt (by linarith [x.2]))
    have hdir : Continuous (fun x : Shell => ‖(x : E3)‖⁻¹ • (x : E3)) :=
      hinv.smul hx
    have hdirS : Continuous (fun x : Shell =>
        (⟨‖(x : E3)‖⁻¹ • (x : E3), by
          rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr (by linarith [x.2]))]
          exact inv_mul_cancel₀ (ne_of_gt (by linarith [x.2]))⟩ : Sphere2)) :=
      hdir.subtype_mk (fun x => by
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (by linarith [x.2]))]
        exact inv_mul_cancel₀ (ne_of_gt (by linarith [x.2])))
    have htime : Continuous (fun x : Shell => rho ‖(x : E3)‖) := by
      dsimp [rho]
      exact (hr.sub continuous_const).min
        ((hr.sub continuous_const).div_const 4)
    have htimeI : Continuous (fun x : Shell =>
        (⟨rho ‖(x : E3)‖, (coord x).2.2.1, (coord x).2.2.2⟩ : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :=
      htime.subtype_mk (fun x => ⟨(coord x).2.2.1, (coord x).2.2.2⟩)
    change Continuous (fun x : Shell => ((coord x).1, (coord x).2))
    exact hdirS.prodMk htimeI

  have hunc_cont : Continuous uncoord := by
    let vec : D → E3 := fun p => sigma (p.2 : ℝ) • (p.1 : E3)
    have hsigma : Continuous (fun p : D => sigma (p.2 : ℝ)) := by
      dsimp [sigma]
      have ht : Continuous (fun p : D => (p.2 : ℝ)) :=
        continuous_subtype_val.comp continuous_snd
      change Continuous (fun p : D =>
        max (1 + (p.2 : ℝ)) (1 + 4 * (p.2 : ℝ)))
      exact (continuous_const.add ht).max
        (continuous_const.add (continuous_const.mul ht))
    have hv : Continuous vec := by
      dsimp [vec]
      exact hsigma.smul (continuous_subtype_val.comp continuous_fst)
    have hSphereNorm (p : D) : ‖(p.1 : E3)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using p.1.2
    have hballProp (p : D) : dist (vec p) (0 : E3) < 3 := by
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hsigmaPos p), hSphereNorm p]
      simpa [hSphereNorm p] using hsigmaLt p
    have hball : Continuous (fun p : D => (⟨vec p, hballProp p⟩ : Ball3)) :=
      hv.subtype_mk hballProp
    have hshellProp (p : D) : (1 / 2 : ℝ) < ‖(vec p : E3)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hsigmaPos p), hSphereNorm p]
      simpa [hSphereNorm p] using hsigmaGt p
    change Continuous (fun p : D =>
      (⟨(⟨vec p, hballProp p⟩ : Ball3), hshellProp p⟩ : Shell))
    exact hball.subtype_mk hshellProp

  have hcoord_left : ∀ x : Shell, uncoord (coord x) = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hr : (1 / 2 : ℝ) < ‖(x : E3)‖ := x.2
    have hr3 : ‖(x : E3)‖ < 3 := by
      have hr3dist : dist (x.1 : E3) (0 : E3) < 3 := x.1.2
      simpa only [dist_zero_right] using hr3dist
    have hσ : sigma (rho ‖(x : E3)‖) = ‖(x : E3)‖ := hrho_sigma _ hr hr3
    dsimp [uncoord, coord]
    rw [hσ]
    have hrne : ‖(x : E3)‖ ≠ 0 := ne_of_gt (by linarith [hr])
    rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]

  have hcoord_right : ∀ p : D, coord (uncoord p) = p := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      have hσpos : 0 < sigma (p.2 : ℝ) := hsigmaPos p
      dsimp [coord, uncoord]
      have hs : ‖(p.1 : E3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using p.1.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσpos, hs, mul_one,
        smul_smul, inv_mul_cancel₀ hσpos.ne', one_smul]
    · apply Subtype.ext
      have hσpos : 0 < sigma (p.2 : ℝ) := hsigmaPos p
      dsimp [coord, uncoord]
      have hs : ‖(p.1 : E3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using p.1.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσpos, hs, mul_one]
      exact hrho_sigma' _ p.2.2.1 p.2.2.2

  let shellHomeo : Shell ≃ₜ D :=
    { toEquiv :=
        { toFun := coord
          invFun := uncoord
          left_inv := hcoord_left
          right_inv := hcoord_right }
      continuous_toFun := hcoord_cont
      continuous_invFun := hunc_cont }

  let innerTo : Inner → Metric.ball (0 : E3) 1 := fun x =>
    ⟨(x.1 : E3), by
      change dist (x.1 : E3) (0 : E3) < 1
      simpa only [dist_zero_right] using x.2⟩
  let innerFrom : Metric.ball (0 : E3) 1 → Inner := fun y => by
    have hy : ‖(y : E3)‖ < 1 := by
      have hyDist : dist (y : E3) (0 : E3) < 1 := y.2
      simpa only [dist_zero_right] using hyDist
    exact ⟨⟨(y : E3), by
      change dist (y : E3) (0 : E3) < 3
      rw [dist_zero_right]
      linarith⟩, hy⟩
  have hinnerLeft : Function.LeftInverse innerFrom innerTo := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hinnerRight : Function.RightInverse innerFrom innerTo := by
    intro y
    apply Subtype.ext
    rfl
  let innerEquiv : Inner ≃ Metric.ball (0 : E3) 1 :=
    { toFun := innerTo
      invFun := innerFrom
      left_inv := hinnerLeft
      right_inv := hinnerRight }
  have hinnerToCont : Continuous innerTo := by
    change Continuous (fun x : Inner =>
      (⟨(x.1 : E3), by
        change dist (x.1 : E3) (0 : E3) < 1
        simpa only [dist_zero_right] using x.2⟩ : Metric.ball (0 : E3) 1))
    have hval : Continuous (fun x : Inner => (x.1 : E3)) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact hval.subtype_mk (fun x => by
      change dist (x.1 : E3) (0 : E3) < 1
      simpa only [dist_zero_right] using x.2)
  have hinnerFromCont : Continuous innerFrom := by
    have hval : Continuous (fun y : Metric.ball (0 : E3) 1 => (y : E3)) :=
      continuous_subtype_val
    have hball3 : Continuous (fun y : Metric.ball (0 : E3) 1 =>
        (⟨(y : E3), by
          have hy : ‖(y : E3)‖ < 1 := by
            have hyDist : dist (y : E3) (0 : E3) < 1 := y.2
            simpa only [dist_zero_right] using hyDist
          change dist (y : E3) (0 : E3) < 3
          rw [dist_zero_right]
          linarith⟩ : Ball3)) :=
      hval.subtype_mk (fun y => by
        have hy : ‖(y : E3)‖ < 1 := by
          have hyDist : dist (y : E3) (0 : E3) < 1 := y.2
          simpa only [dist_zero_right] using hyDist
        change dist (y : E3) (0 : E3) < 3
        rw [dist_zero_right]
        linarith)
    change Continuous (fun y : Metric.ball (0 : E3) 1 =>
      (⟨(⟨(y : E3), by
          have hy : ‖(y : E3)‖ < 1 := by
            have hyDist : dist (y : E3) (0 : E3) < 1 := y.2
            simpa only [dist_zero_right] using hyDist
          change dist (y : E3) (0 : E3) < 3
          rw [dist_zero_right]
          linarith⟩ : Ball3), by
        have hyDist : dist (y : E3) (0 : E3) < 1 := y.2
        simpa only [dist_zero_right] using hyDist⟩ : Inner))
    exact hball3.subtype_mk (fun y => by
      have hyDist : dist (y : E3) (0 : E3) < 1 := y.2
      simpa only [dist_zero_right] using hyDist)
  let InnerHomeo : Inner ≃ₜ Metric.ball (0 : E3) 1 :=
    Homeomorph.mk innerEquiv hinnerToCont hinnerFromCont

  let innerMap : Inner → CappedSpace c.boundaryMap := fun x => capInterior c (InnerHomeo x)
  have hinnerEmb : Topology.IsOpenEmbedding innerMap := by
    change Topology.IsOpenEmbedding (capInterior c ∘ InnerHomeo)
    exact hcapEmb.comp InnerHomeo.isOpenEmbedding

  let shellMap : Shell → CappedSpace c.boundaryMap := fun x => seamChart (shellHomeo x)
  have hshellEmb : Topology.IsOpenEmbedding shellMap := by
    change Topology.IsOpenEmbedding (seamChart ∘ shellHomeo)
    exact hseamChart.comp shellHomeo.isOpenEmbedding

  let q : c.carrier ⊕ Ball → CappedSpace c.boundaryMap := Quot.mk (capSeam c.boundaryMap)
  let R : (c.carrier ⊕ Ball) → (c.carrier ⊕ Ball) → Prop := fun x y =>
    x = y ∨
      (∃ s : Sphere2, x = Sum.inl (c.boundaryMap s) ∧ y = Sum.inr (boundary s)) ∨
      (∃ s : Sphere2, x = Sum.inr (boundary s) ∧ y = Sum.inl (c.boundaryMap s))
  have hboundary_inj : Function.Injective (boundary : Sphere2 → Ball) := by
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
        · have hst' : c.boundaryMap s = c.boundaryMap t := Sum.inl.inj (hy.symm.trans hy')
          have hst : s = t := c.boundaryEmbedding.injective hst'
          subst t
          exact Or.inl (hx.trans hz'.symm)
        · cases hy.symm.trans hy'
  have hseam_R : ∀ x y, capSeam c.boundaryMap x y → R x y := by
    intro x y h
    rcases h with ⟨s, hx, hy⟩
    exact Or.inr (Or.inl ⟨s, hx, hy⟩)
  have hgen : ∀ x y, Relation.EqvGen (capSeam c.boundaryMap) x y ↔ R x y := by
    intro x y
    constructor
    · intro h
      induction h with
      | rel a b hab => exact hseam_R a b hab
      | refl a => exact Or.inl rfl
      | symm a b hab ih => exact hR_equiv.symm ih
      | trans a b d hab hbd ihab ihbd => exact hR_equiv.trans ihab ihbd
    · intro h
      rcases h with h | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
      · cases h
        exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ ⟨s, hx, hy⟩
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨s, hy, hx⟩)
  have hquot : ∀ x y, q x = q y ↔ R x y := by
    intro x y
    constructor
    · intro h
      exact (hgen x y).mp (Quot.eqvGen_exact h)
    · intro h
      exact Quot.eqvGen_sound ((hgen x y).mpr h)

  let f : Ball3 → CappedSpace c.boundaryMap := fun x =>
    if hx : ‖(x : E3)‖ ≤ 1 then
      q (Sum.inr (⟨(x : E3), by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hx⟩ : Ball))
    else
      shellMap ⟨x, by
        have hx' : 1 < ‖(x : E3)‖ := lt_of_not_ge hx
        linarith⟩

  have hcap_shell : ∀ x : Shell, (hx : ‖(x : E3)‖ ≤ 1) →
      q (Sum.inr (⟨(x : E3), by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hx⟩ : Ball)) = shellMap x := by
    intro x hx
    let d := shellHomeo x
    have htime : (d.2 : ℝ) = ‖(x : E3)‖ - 1 := by
      dsimp [d, shellHomeo, coord, rho]
      rw [min_eq_left (by linarith : ‖(x : E3)‖ - 1 ≤ (‖(x : E3)‖ - 1) / 4)]
    have htime0 : (d.2 : ℝ) ≤ 0 := by rw [htime]; linarith
    have hunit : (d.1 : E3) = ‖(x : E3)‖⁻¹ • (x : E3) := rfl
    rw [show shellMap x = seamChart d by rfl, hseamNeg d.1 d.2 htime0]
    apply congrArg (fun z : Ball => q (Sum.inr z))
    apply Subtype.ext
    change (x : E3) = (1 + (d.2 : ℝ)) • (d.1 : E3)
    rw [hunit, htime, show 1 + (‖(x : E3)‖ - 1) = ‖(x : E3)‖ by ring]
    have hxne : ‖(x : E3)‖ ≠ 0 := ne_of_gt (by linarith [x.2])
    rw [smul_smul, mul_inv_cancel₀ hxne, one_smul]

  have hf_inner : ∀ x : Inner, f x.1 = innerMap x := by
    intro x
    have hx : ‖(x.1 : E3)‖ ≤ 1 := le_of_lt x.2
    have hfx : f x.1 = q (Sum.inr (⟨(x.1 : E3), by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hx⟩ : Ball)) := by
      simp [f, hx]
    rw [hfx]
    change Quot.mk (capSeam c.boundaryMap) (Sum.inr (⟨(x.1 : E3), by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hx⟩ : Ball)) =
      Quot.mk (capSeam c.boundaryMap) (Sum.inr
        (PoincareConjecture.ParallelImplementation.CappedSpaceTopology.interiorPoint
          (InnerHomeo x)))
    apply congrArg (fun z : Ball => Quot.mk (capSeam c.boundaryMap) (Sum.inr z))
    apply Subtype.ext
    rfl

  have hf_shell : ∀ x : Shell, f x.1 = shellMap x := by
    intro x
    by_cases hx : ‖(x : E3)‖ ≤ 1
    · simpa [f, hx] using hcap_shell x hx
    · simp [f, hx]

  have hf_inner_cont : ContinuousOn f {x : Ball3 | ‖(x : E3)‖ < 1} := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun x : Inner => f x.1)
    have heq : (fun x : Inner => f x.1) = innerMap := funext hf_inner
    rw [heq]
    exact hinnerEmb.continuous

  have hf_shell_cont : ContinuousOn f {x : Ball3 | (1 / 2 : ℝ) < ‖(x : E3)‖} := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun x : Shell => f x.1)
    have heq : (fun x : Shell => f x.1) = shellMap := funext hf_shell
    rw [heq]
    exact hshellEmb.continuous

  have hf_cont : Continuous f := by
    apply continuous_of_cover_nhds (s := fun i : Bool =>
      if i then {x : Ball3 | ‖(x : E3)‖ < 1}
      else {x : Ball3 | (1 / 2 : ℝ) < ‖(x : E3)‖})
    · intro x
      by_cases hx : ‖(x : E3)‖ < 1
      · refine ⟨true, ?_⟩
        exact (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const).mem_nhds hx
      · refine ⟨false, ?_⟩
        have hx' : 1 ≤ ‖(x : E3)‖ := le_of_not_gt hx
        have hs : (1 / 2 : ℝ) < ‖(x : E3)‖ := by linarith
        exact (isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)).mem_nhds hs
    · intro i
      cases i
      · exact hf_shell_cont
      · exact hf_inner_cont

  have hcross : ∀ (x : Ball3) (hx : ‖(x : E3)‖ ≤ 1)
      (y : Ball3) (hy : 1 < ‖(y : E3)‖), f x = f y → False := by
    intro x hx y hy hxy
    let sy : Shell := ⟨y, by linarith⟩
    let d := shellHomeo sy
    have htpos : 0 < (d.2 : ℝ) := by
      have hr : (1 / 2 : ℝ) < ‖(y : E3)‖ := by linarith
      have hr3 : ‖(y : E3)‖ < 3 := by
        have hyDist : dist (y : E3) (0 : E3) < 3 := y.2
        simpa only [dist_zero_right] using hyDist
      have hh := hrho_sigma _ hr hr3
      have htime : (d.2 : ℝ) = (‖(y : E3)‖ - 1) / 4 := by
        dsimp [d, shellHomeo, coord, rho]
        rw [min_eq_right (by linarith : (‖(y : E3)‖ - 1) / 4 ≤ ‖(y : E3)‖ - 1)]
      rw [htime]
      positivity
    have hfy : f y = q (Sum.inl
        (c.collar (d.1, ⟨(d.2 : ℝ), le_of_lt htpos,
          lt_trans d.2.2.2 (by norm_num)⟩))) := by
      change f sy.1 = _
      calc
        f sy.1 = shellMap sy := hf_shell sy
        _ = seamChart d := rfl
        _ = q (Sum.inl (c.collar (d.1, ⟨(d.2 : ℝ), le_of_lt htpos,
          lt_trans d.2.2.2 (by norm_num)⟩))) := hseamPos d.1 d.2 (le_of_lt htpos)
    have hfx : f x = q (Sum.inr (⟨(x : E3), by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx⟩ : Ball)) := by
      simp [f, hx]
    have hR := (hquot (Sum.inr (⟨(x : E3), by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx⟩ : Ball))
      (Sum.inl (c.collar (d.1, ⟨(d.2 : ℝ), le_of_lt htpos,
        lt_trans d.2.2.2 (by norm_num)⟩)))).mp (hfx.symm.trans (hxy.trans hfy))
    rcases hR with hEq | ⟨s, hbad, _⟩ | ⟨s, hball, hcollar⟩
    · cases hEq
    · cases hbad
    · have hnorms : ‖(x : E3)‖ = 1 := by
        have hv := congrArg (fun z : Ball => ‖(z : E3)‖) (Sum.inr.inj hball)
        have hs : ‖(s : E3)‖ = 1 := by
          simpa [Metric.mem_sphere, dist_zero_right] using s.2
        have hboundaryNorm : ‖(boundary s : E3)‖ = 1 := by
          change ‖(s : E3)‖ = 1
          exact hs
        rw [hboundaryNorm] at hv
        exact hv
      have hzero : c.collar (s, ⟨(0 : ℝ), by norm_num, by norm_num⟩) =
          c.boundaryMap s := c.collarZero s
      have hparam : (d.1, ⟨(d.2 : ℝ), le_of_lt htpos,
          lt_trans d.2.2.2 (by norm_num)⟩) =
          (s, (⟨0, by norm_num, by norm_num⟩ : Set.Ico (0 : ℝ) 1)) :=
        c.collarEmbedding.injective ((Sum.inl.inj hcollar).trans hzero.symm)
      have htzero : (d.2 : ℝ) = 0 := by
        have h := congrArg (fun z : Sphere2 × Set.Ico (0 : ℝ) 1 => (z.2 : ℝ)) hparam
        simpa using h
      linarith

  have hf_inj : Function.Injective f := by
    intro x y hxy
    by_cases hx : ‖(x : E3)‖ ≤ 1
    · by_cases hy : ‖(y : E3)‖ ≤ 1
      · have hR := (hquot
          (Sum.inr (⟨(x : E3), by rw [Metric.mem_closedBall, dist_zero_right]; exact hx⟩ : Ball))
          (Sum.inr (⟨(y : E3), by rw [Metric.mem_closedBall, dist_zero_right]; exact hy⟩ : Ball))).mp
            (by simpa [f, hx, hy] using hxy)
        rcases hR with h | ⟨_, hbad, _⟩ | ⟨_, _, hbad⟩
        · have hv := Sum.inr.inj h
          apply Subtype.ext
          exact congrArg (fun z : Ball => (z : E3)) hv
        · cases hbad
        · cases hbad
      · exact False.elim (hcross x hx y (lt_of_not_ge hy) hxy)
    · have hx' : 1 < ‖(x : E3)‖ := lt_of_not_ge hx
      by_cases hy : ‖(y : E3)‖ ≤ 1
      · exact False.elim (hcross y hy x hx' hxy.symm)
      · have hy' : 1 < ‖(y : E3)‖ := lt_of_not_ge hy
        let sx : Shell := ⟨x, by linarith⟩
        let sy : Shell := ⟨y, by linarith⟩
        have hxy' : shellMap sx = shellMap sy := by
          simpa [f, hx, hy] using hxy
        have h := hshellEmb.injective hxy'
        exact congrArg Subtype.val h

  have hInnerOpen : IsOpen {x : Ball3 | ‖(x : E3)‖ < 1} :=
    isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  have hShellOpen : IsOpen {x : Ball3 | (1 / 2 : ℝ) < ‖(x : E3)‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
  have hf_open : IsOpenMap f := by
    intro U hU
    let Ui : Set Inner := (Subtype.val : Inner → Ball3) ⁻¹' U
    let Us : Set Shell := (Subtype.val : Shell → Ball3) ⁻¹' U
    have hUi : IsOpen Ui := continuous_subtype_val.isOpen_preimage _ hU
    have hUs : IsOpen Us := continuous_subtype_val.isOpen_preimage _ hU
    have hi : IsOpen (innerMap '' Ui) := hinnerEmb.isOpenMap _ hUi
    have hs : IsOpen (shellMap '' Us) := hshellEmb.isOpenMap _ hUs
    have hcover : f '' U = innerMap '' Ui ∪ shellMap '' Us := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        by_cases hxI : ‖(x : E3)‖ < 1
        · exact Or.inl ⟨⟨x, hxI⟩, by simpa [Ui] using hx,
            (hf_inner ⟨x, hxI⟩).symm⟩
        · have hxS : (1 / 2 : ℝ) < ‖(x : E3)‖ := by
            have hh : 1 ≤ ‖(x : E3)‖ := le_of_not_gt hxI
            linarith
          exact Or.inr ⟨⟨x, hxS⟩, by simpa [Us] using hx,
            (hf_shell ⟨x, hxS⟩).symm⟩
      · intro hz
        rcases hz with hz | hz
        · rcases hz with ⟨x, hx, hxy⟩
          have hxU : x.1 ∈ U := by simpa [Ui] using hx
          exact ⟨x.1, hxU, (hf_inner x).trans hxy⟩
        · rcases hz with ⟨x, hx, hxy⟩
          have hxU : x.1 ∈ U := by simpa [Us] using hx
          exact ⟨x.1, hxU, (hf_shell x).trans hxy⟩
    rw [hcover]
    exact hi.union hs

  have hfEmb : Topology.IsOpenEmbedding f :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf_cont hf_inj hf_open

  letI : Nonempty Ball3 := ⟨⟨0, by simp [Ball3, Metric.mem_ball]⟩⟩
  letI : Nonempty (CappedSpace c.boundaryMap) :=
    ⟨Quot.mk (capSeam c.boundaryMap)
      (Sum.inr (⟨0, by simp [Ball, Metric.mem_closedBall]⟩ : Ball))⟩
  let e0 : OpenPartialHomeomorph Ball3 (CappedSpace c.boundaryMap) :=
    hfEmb.toOpenPartialHomeomorph f
  have hBall3Open : IsOpen (Metric.ball (0 : E3) 3) := Metric.isOpen_ball
  let e : OpenPartialHomeomorph E3 (CappedSpace c.boundaryMap) :=
    e0.lift_openEmbedding hBall3Open.isOpenEmbedding_subtypeVal
  refine ⟨e, ?_, ?_⟩
  · have heSource : e.source = Set.range (Subtype.val : Ball3 → E3) := by
      ext x
      simp [e, e0, Ball3, Metric.mem_ball, dist_zero_right]
    rw [heSource]
    intro x hx
    have hxnorm : ‖x‖ ≤ 2 := by
      have hdist : dist x (0 : E3) ≤ 2 := hx
      simpa only [dist_zero_right] using hdist
    exact ⟨⟨x, by
      rw [Metric.mem_ball, dist_zero_right]
      linarith⟩, rfl⟩
  · intro x hx
    have hxnorm : ‖x‖ ≤ 1 := by
      have hdist : dist x (0 : E3) ≤ 1 := hx
      simpa only [dist_zero_right] using hdist
    have hx3 : ‖x‖ < 3 := lt_of_le_of_lt hxnorm (by norm_num)
    have hformula : f ⟨x, by rw [Metric.mem_ball, dist_zero_right]; exact hx3⟩ =
        q (Sum.inr (⟨x, by rw [Metric.mem_closedBall, dist_zero_right]; exact hxnorm⟩ : Ball)) := by
      simp [f, hxnorm]
    let x3 : Ball3 := ⟨x, by rw [Metric.mem_ball, dist_zero_right]; exact hx3⟩
    calc
      e x = f x3 := by
        change (e0.lift_openEmbedding hBall3Open.isOpenEmbedding_subtypeVal) (x3 : E3) = f x3
        rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
        simp [e0]
      _ = q (Sum.inr (⟨x, by rw [Metric.mem_closedBall, dist_zero_right]; exact hxnorm⟩ : Ball)) := hformula
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedCapChart
