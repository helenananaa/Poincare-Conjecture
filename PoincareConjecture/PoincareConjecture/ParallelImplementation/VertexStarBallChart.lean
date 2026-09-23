import PoincareConjecture.ParallelImplementation.PuncturedStarHomeomorph
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.VertexStarBallChart
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open scoped BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** A spherical vertex link gives an actual Euclidean ball chart for the full open star. -/
theorem vertex_star_homeomorph_ball_of_spherical_link
    {V : Type*} [Fintype V] [DecidableEq V] (K : FiniteAbstractComplex V)
    (v : V) (hv : ({v} : Finset V) ∈ K.faces)
    (eLink : {y : V → ℝ // (∀ w, 0 ≤ y w) ∧ (∑ w, y w) = 1 ∧
      (Finset.univ.filter (fun w => 0 < y w)) ∈ (abstractLink K {v} hv).faces} ≃ₜ
      {z : E3 // ‖z‖ = 1}) :
    Nonempty ({x : V → ℝ // x ∈ (realization K).space ∧ 0 < x v} ≃ₜ
      {z : E3 // ‖z‖ < 1}) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let X := {x : V → ℝ // x ∈ (realization K).space ∧ 0 < x v}
  let Z := {z : E3 // ‖z‖ < 1}
  let Y := {y : V → ℝ // (∀ w, 0 ≤ y w) ∧ (∑ w, y w) = 1 ∧
    (Finset.univ.filter (fun w => 0 < y w)) ∈ (abstractLink K {v} hv).faces}
  let P := Set.Ioo (0 : ℝ) 1 × Y
  obtain ⟨e, he⟩ :=
    PoincareConjecture.ParallelImplementation.PuncturedStarHomeomorph.exists_punctured_star_homeomorph
      K v hv
  let s0 : {z : E3 // ‖z‖ = 1} :=
    ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp⟩
  let y0 : Y := eLink.symm s0
  let d : X → Y := fun x =>
    if hx : x.1 v < 1 then
      (e ⟨x.1, x.2.1, x.2.2, hx⟩).2
    else y0
  let dir : ∀ z : Z, 0 < ‖z.1‖ → {u : E3 // ‖u‖ = 1} := fun z hz =>
    ⟨(‖z.1‖)⁻¹ • z.1, by
      have hz' : ‖z.1‖ = ‖z.1‖ := rfl
      calc
        ‖(‖z.1‖)⁻¹ • z.1‖ = ‖(‖z.1‖)⁻¹‖ * ‖z.1‖ := norm_smul _ _
        _ = (‖z.1‖)⁻¹ * ‖z.1‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hz)]
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hz)⟩
  let ydir : Z → Y := fun z =>
    if hz : 0 < ‖z.1‖ then eLink.symm (dir z hz) else y0
  let Fval : X → E3 := fun x => (1 - x.1 v) • (eLink (d x)).1
  let Gval : Z → V → ℝ := fun z w =>
    if w = v then 1 - ‖z.1‖ else ‖z.1‖ * (ydir z).1 w
  have hvle (x : X) : x.1 v ≤ 1 := by
    rcases PoincareConjecture.ParallelImplementation.BarycentricMembership.mem_realization_iff_barycentric
      K x.1 |>.mp x.2.1 with ⟨hn, hs, _⟩
    have hle := Finset.single_le_sum (s := Finset.univ) (f := x.1)
      (fun w hw => hn w) (Finset.mem_univ v)
    simpa [hs] using hle
  have hvertex (x : X) (hxv : x.1 v = 1) :
      x.1 = barycentricVertex v := by
    rcases PoincareConjecture.ParallelImplementation.BarycentricMembership.mem_realization_iff_barycentric
      K x.1 |>.mp x.2.1 with ⟨hn, hs, _⟩
    have herase : (∑ w ∈ Finset.univ.erase v, x.1 w) = 0 := by
      have hsum := Finset.univ.sum_erase_add x.1 (Finset.mem_univ v)
      rw [hs, hxv] at hsum
      linarith
    funext w
    by_cases hw : w = v
    · subst w
      simp [barycentricVertex, hxv]
    · have hmem : w ∈ Finset.univ.erase v :=
        Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩
      have hle := Finset.single_le_sum (s := Finset.univ.erase v) (f := x.1)
        (fun u hu => hn u) hmem
      rw [herase] at hle
      have hwzero : x.1 w = 0 := le_antisymm hle (hn w)
      simp [barycentricVertex, hw, hwzero]
  have hvreal : barycentricVertex v ∈ (realization K).space := by
    apply PoincareConjecture.ParallelImplementation.BarycentricMembership.mem_realization_iff_barycentric
      K (barycentricVertex v) |>.2
    refine ⟨?_, ?_, ?_⟩
    · intro w
      by_cases hw : w = v <;> simp [barycentricVertex, hw]
    · simp [barycentricVertex, Pi.single_apply]
    · have hs : Finset.univ.filter (fun w => 0 < barycentricVertex v w) = {v} := by
        ext w
        by_cases hw : w = v <;> simp [barycentricVertex, Pi.single_apply, hw]
      rw [hs]
      exact hv
  have hdirnorm (z : Z) (hz : 0 < ‖z.1‖) :
      ‖(dir z hz).1‖ = 1 := (dir z hz).2
  have hFnorm (x : X) : ‖Fval x‖ = 1 - x.1 v := by
    change ‖(1 - x.1 v) • (eLink (d x)).1‖ = 1 - x.1 v
    rw [norm_smul, (eLink (d x)).2]
    simp only [mul_one, Real.norm_eq_abs]
    exact abs_of_nonneg (sub_nonneg.mpr (hvle x))
  have hFball (x : X) : ‖Fval x‖ < 1 := by
    rw [hFnorm]
    linarith [x.2.2]
  let F : X → Z := fun x => ⟨Fval x, hFball x⟩
  have hy0props : (∀ w, 0 ≤ y0.1 w) ∧ (∑ w, y0.1 w) = 1 :=
    ⟨y0.2.1, y0.2.2.1⟩
  have hGmem (z : Z) : Gval z ∈ (realization K).space ∧ 0 < Gval z v := by
    by_cases hz : 0 < ‖z.1‖
    · let t : ℝ := 1 - ‖z.1‖
      have ht0 : 0 < t := by dsimp [t]; linarith [z.2]
      have ht1 : t < 1 := by dsimp [t]; linarith
      have hy := (ydir z).2
      have hcoords : Gval z = fun w =>
          if w = v then t else (1 - t) * (ydir z).1 w := by
        funext w
        by_cases hw : w = v
        · simp [Gval, hw, t]
        · simp [Gval, hw, t]
      have hrec :=
        PoincareConjecture.ParallelImplementation.BarycentricLinkReconstruction.reconstruct_from_link_coordinates
          K v hv (ydir z).1 hy.1 hy.2.1 hy.2.2
          t ht0 ht1
      rw [hcoords]
      exact ⟨hrec.1, by simpa [t] using ht0⟩
    · have hr0 : ‖z.1‖ = 0 := le_antisymm (le_of_not_gt hz) (norm_nonneg _)
      have hcoords : Gval z = barycentricVertex v := by
        funext w
        by_cases hw : w = v
        · subst w
          simp [Gval, hr0, barycentricVertex]
        · simp [Gval, hw, hr0, barycentricVertex]
      rw [hcoords]
      exact ⟨hvreal, by simp [barycentricVertex, Pi.single_apply]⟩
  let G : Z → X := fun z => ⟨Gval z, hGmem z⟩

  let U : Set X := {x | x.1 v < 1}
  let qU : U → {x : V → ℝ // x ∈ (realization K).space ∧
      0 < x v ∧ x v < 1} := fun u => ⟨u.1.1, u.1.2.1, u.1.2.2, u.2⟩
  let dU : U → Y := fun u => (e (qU u)).2
  have hqU : Continuous qU := by
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hdU : Continuous dU := by
    exact (continuous_snd.comp e.continuous).comp hqU
  have hdrestrict : U.restrict d = dU := by
    funext u
    have hu : u.1.1 v < 1 := by
      have h := u.2
      change u.1.1 v < 1 at h
      exact h
    change (if h : u.1.1 v < 1 then
      (e ⟨u.1.1, u.1.2.1, u.1.2.2, h⟩).2 else y0) = _
    rw [dif_pos hu]
  have hdOn : ContinuousOn d U := by
    rw [continuousOn_iff_continuous_restrict]
    rw [hdrestrict]
    exact hdU
  have hUopen : IsOpen U := by
    exact isOpen_lt ((continuous_apply v).comp continuous_subtype_val) continuous_const
  let Fnear : U → E3 := fun u => (1 - u.1.1 v) • (eLink (dU u)).1
  have hFnear : Continuous Fnear := by
    have hcoord : Continuous (fun u : U => u.1.1 v) :=
      (continuous_apply v).comp (continuous_subtype_val.comp continuous_subtype_val)
    have hvec : Continuous (fun u : U => (eLink (dU u)).1) :=
      (continuous_subtype_val.comp eLink.continuous).comp hdU
    exact (continuous_const.sub hcoord).smul hvec
  have hFrestrict : U.restrict Fval = Fnear := by
    funext u
    change (1 - u.1.1 v) • (eLink (d u.1)).1 = _
    rw [show d u.1 = dU u from congrFun hdrestrict u]
  have hFOn : ContinuousOn Fval U := by
    rw [continuousOn_iff_continuous_restrict]
    rw [hFrestrict]
    exact hFnear
  have hradX : Continuous (fun x : X => 1 - x.1 v) :=
    continuous_const.sub ((continuous_apply v).comp continuous_subtype_val)
  have hFcenter (x : X) (hxv : x.1 v = 1) : ContinuousAt Fval x := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hball0 : ∀ᶠ y : ℝ in nhds (0 : ℝ), |y| < ε := by
      filter_upwards [Metric.ball_mem_nhds 0 hε] with y hy
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs] using hy
    have hball : ∀ᶠ y : ℝ in nhds (1 - x.1 v), |y| < ε := by
      simpa [hxv] using hball0
    have hevent := (hradX.continuousAt (x := x)).eventually hball
    filter_upwards [hevent] with x' hx'
    have hFx : Fval x = 0 := by simp [Fval, hxv]
    have hdist : dist (Fval x') 0 = dist (1 - x'.1 v) 0 := by
      rw [dist_eq_norm, dist_eq_norm, sub_zero, sub_zero, hFnorm]
      simp [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hvle x'))]
    rw [hFx, hdist]
    simpa [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hx'
  have hFvalcont : Continuous Fval := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x.1 v < 1
    · exact hFOn.continuousAt (IsOpen.mem_nhds hUopen hx)
    · have hxv : x.1 v = 1 := le_antisymm (hvle x) (le_of_not_gt hx)
      exact hFcenter x hxv
  have hFcont : Continuous F := by
    change Continuous (fun x => (⟨Fval x, hFball x⟩ : Z))
    exact hFvalcont.subtype_mk _

  let W : Set Z := {z | 0 < ‖z.1‖}
  have hnormZ : Continuous (fun z : Z => ‖z.1‖) :=
    continuous_norm.comp continuous_subtype_val
  have hWopen : IsOpen W := isOpen_lt continuous_const hnormZ
  let dW : W → Y := fun z => eLink.symm (dir z.1 z.2)
  have hdirW : Continuous (fun z : W => dir z.1 z.2) := by
    have hr : Continuous (fun z : W => ‖z.1.1‖) :=
      continuous_norm.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hinv : Continuous (fun z : W => (‖z.1.1‖)⁻¹) := by
      exact hr.inv₀ (fun z => ne_of_gt z.2)
    have hvec : Continuous (fun z : W => z.1.1) :=
      continuous_subtype_val.comp continuous_subtype_val
    change Continuous (fun z : W =>
      (⟨(‖z.1.1‖)⁻¹ • z.1.1, _⟩ : {u : E3 // ‖u‖ = 1}))
    exact (hinv.smul hvec).subtype_mk _
  have hdW : Continuous dW := eLink.symm.continuous.comp hdirW
  have hypos : W.restrict ydir = dW := by
    funext z
    have hzpos : 0 < ‖z.1.1‖ := by
      have h := z.2
      change 0 < ‖z.1.1‖ at h
      exact h
    change ydir z.1 = eLink.symm (dir z.1 hzpos)
    dsimp [ydir]
    rw [dif_pos hzpos]
  let Gnear : W → V → ℝ := fun z w =>
    if w = v then 1 - ‖z.1.1‖ else ‖z.1.1‖ * (dW z).1 w
  have hGnear : Continuous Gnear := by
    apply continuous_pi
    intro w
    by_cases hw : w = v
    · simp [Gnear, hw]
      exact continuous_const.sub (hnormZ.comp continuous_subtype_val)
    · simp [Gnear, hw]
      exact (hnormZ.comp continuous_subtype_val).mul
        ((continuous_apply w).comp (continuous_subtype_val.comp hdW))
  have hGrestrict : W.restrict Gval = Gnear := by
    funext z
    have hzdir : ydir z.1 = dW z := congrFun hypos z
    funext w
    simp [Gval, Gnear, hzdir]
  have hGOn : ContinuousOn Gval W := by
    rw [continuousOn_iff_continuous_restrict]
    rw [hGrestrict]
    exact hGnear
  have hGvalcenter (z : Z) (hz0 : ‖z.1‖ = 0) : ContinuousAt Gval z := by
    have hrcont : Continuous (fun z : Z => ‖z.1‖) := hnormZ
    have hrT := hrcont.continuousAt (x := z)
    have hcoords : ∀ w, Filter.Tendsto (fun z' : Z => Gval z' w) (nhds z)
        (nhds (barycentricVertex v w)) := by
      intro w
      by_cases hw : w = v
      · subst w
        have hscalarCont : Continuous (fun z' : Z => (1 : ℝ) - ‖z'.1‖) :=
          continuous_const.sub hrcont
        have hscalar : Filter.Tendsto (fun z' : Z => 1 - ‖z'.1‖)
            (nhds z) (nhds 1) := by
          simpa only [ContinuousAt, hz0, sub_zero] using hscalarCont.continuousAt (x := z)
        simpa [Gval, barycentricVertex, Pi.single_apply] using hscalar
      · apply Metric.tendsto_nhds.mpr
        intro ε hε
        have hball0 : ∀ᶠ y : ℝ in nhds (0 : ℝ), |y| < ε := by
          filter_upwards [Metric.ball_mem_nhds 0 hε] with y hy
          simpa [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs] using hy
        have hball : ∀ᶠ y : ℝ in nhds (‖z.1‖), |y| < ε := by
          simpa [hz0] using hball0
        have hevent := hrT.eventually hball
        filter_upwards [hevent] with z' hz'
        have hrle : 0 ≤ ‖z'.1‖ := norm_nonneg _
        have hy0' : 0 ≤ (ydir z').1 w := (ydir z').2.1 w
        have hy1' : (ydir z').1 w ≤ 1 := by
          have hsingle := Finset.single_le_sum (s := Finset.univ)
            (f := (ydir z').1) (fun u hu => (ydir z').2.1 u)
            (Finset.mem_univ w)
          simpa [(ydir z').2.2.1] using hsingle
        have hbound : |Gval z' w| ≤ ‖z'.1‖ := by
          have hnonneg : 0 ≤ ‖z'.1‖ * (ydir z').1 w := mul_nonneg hrle hy0'
          have hfactor : 0 ≤ 1 - (ydir z').1 w := by linarith [hy1']
          have hle : ‖z'.1‖ * (ydir z').1 w ≤ ‖z'.1‖ := by
            nlinarith [mul_nonneg hrle hfactor]
          dsimp only [Gval]
          rw [if_neg hw]
          rw [abs_of_nonneg hnonneg]
          exact hle
        have hsmall : ‖z'.1‖ < ε := by
          simpa [abs_of_nonneg (norm_nonneg _)] using hz'
        rw [dist_eq_norm]
        simp only [barycentricVertex, Pi.single_apply, if_neg hw, sub_zero,
          Real.norm_eq_abs]
        exact lt_of_le_of_lt hbound hsmall
    have hpi : Filter.Tendsto Gval (nhds z)
        (nhds (barycentricVertex v)) :=
      tendsto_pi_nhds.2 hcoords
    have hzval : Gval z = barycentricVertex v := by
      funext w
      by_cases hw : w = v
      · subst w
        simp [Gval, hz0, barycentricVertex, Pi.single_apply]
      · simp [Gval, hw, hz0, barycentricVertex, Pi.single_apply]
    change Filter.Tendsto Gval (nhds z) (nhds (Gval z))
    rw [hzval]
    exact hpi
  have hGvalcont : Continuous Gval := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : 0 < ‖z.1‖
    · exact hGOn.continuousAt (IsOpen.mem_nhds hWopen hz)
    · have hz0 : ‖z.1‖ = 0 := le_antisymm (le_of_not_gt hz) (norm_nonneg _)
      exact hGvalcenter z hz0
  have hGcont : Continuous G := by
    change Continuous (fun z => (⟨Gval z, hGmem z⟩ : X))
    exact hGvalcont.subtype_mk _

  have hGF : ∀ x : X, G (F x) = x := by
    intro x
    apply Subtype.ext
    change Gval (F x) = x.1
    by_cases hxv : x.1 v = 1
    · have hfx : Fval x = 0 := by
        simp [Fval, hxv]
      have hgx : Gval (F x) = barycentricVertex v := by
        funext w
        by_cases hw : w = v
        · subst w
          simp [Gval, F, hfx, barycentricVertex, Pi.single_apply]
        · simp [Gval, hw, F, hfx, barycentricVertex, Pi.single_apply]
      rw [hgx, hvertex x hxv]
    · have hxlt : x.1 v < 1 := lt_of_le_of_ne (hvle x) hxv
      let px : {x : V → ℝ // x ∈ (realization K).space ∧
        0 < x v ∧ x v < 1} := ⟨x.1, x.2.1, x.2.2, hxlt⟩
      let yy : Y := (e px).2
      have hr : 0 < 1 - x.1 v := sub_pos.mpr hxlt
      have hnormfx : ‖(F x).1‖ = 1 - x.1 v := by
        simpa [F] using hFnorm x
      have hdirfx : dir (F x) (by rw [hnormfx]; exact hr) = eLink yy := by
        apply Subtype.ext
        change (‖(F x).1‖)⁻¹ • (F x).1 = (eLink yy).1
        rw [hnormfx]
        have hsmul : Fval x = (1 - x.1 v) • (eLink yy).1 := by
          simp [Fval, d, yy, px, hxlt]
        change (1 - x.1 v)⁻¹ • Fval x = (eLink yy).1
        rw [hsmul]
        calc
          (1 - x.1 v)⁻¹ • ((1 - x.1 v) • (eLink yy).1) =
              ((1 - x.1 v)⁻¹ * (1 - x.1 v)) • (eLink yy).1 := by rw [smul_smul]
          _ = (eLink yy).1 := by simp [ne_of_gt hr]
      have hyy : ydir (F x) = yy := by
        change (if h : 0 < ‖(F x).1‖ then eLink.symm (dir (F x) h) else y0) = yy
        rw [dif_pos (by rw [hnormfx]; exact hr)]
        rw [hdirfx]
        exact eLink.symm_apply_apply yy
      have hep := he px
      funext w
      by_cases hw : w = v
      · subst w
        simp [Gval, F, hnormfx]
      · have hnormcoord := congrFun hep.2 w
        simp [hw] at hnormcoord
        simp only [Gval, if_neg hw]
        rw [hnormfx, hyy]
        have hrw : 1 - x.1 v ≠ 0 := ne_of_gt hr
        calc
          (1 - x.1 v) * yy.1 w =
              (1 - x.1 v) * (x.1 w / (1 - x.1 v)) := by rw [hnormcoord]
          _ = x.1 w := by
            rw [mul_comm]
            exact div_mul_cancel₀ _ hrw
  have hFG : ∀ z : Z, F (G z) = z := by
    intro z
    apply Subtype.ext
    change Fval (G z) = z.1
    by_cases hz : 0 < ‖z.1‖
    · let t : ℝ := 1 - ‖z.1‖
      have ht0 : 0 < t := by dsimp [t]; linarith [z.2]
      have ht1 : t < 1 := by dsimp [t]; linarith [hz]
      let p : P := (⟨t, ht0, ht1⟩, ydir z)
      let q : {x : V → ℝ // x ∈ (realization K).space ∧
        0 < x v ∧ x v < 1} := e.symm p
      have hq : e q = p := by simp [q]
      have hqv : q.1 v = t := by
        have h := (he q).1
        simpa [hq, p, t] using h.symm
      have hqy : (ydir z).1 = fun w =>
          if w = v then 0 else q.1 w / (1 - q.1 v) := by
        have h := (he q).2
        simpa [hq, p] using h
      have hqcoords : q.1 = Gval z := by
        funext w
        by_cases hw : w = v
        · subst w
          simp [Gval, t, hqv]
        · have hcoord := congrFun hqy w
          simp [hw] at hcoord
          have hden : 1 - q.1 v = ‖z.1‖ := by
            rw [hqv]
            dsimp [t]
            ring
          rw [hden] at hcoord
          have hmul : (ydir z).1 w * ‖z.1‖ = q.1 w := by
            calc
              (ydir z).1 w * ‖z.1‖ =
                  (q.1 w / ‖z.1‖) * ‖z.1‖ := by rw [← hcoord]
              _ = q.1 w := div_mul_cancel₀ _ (ne_of_gt hz)
          simp [Gval, hw, hmul, mul_comm]
      have hGv : Gval z v = t := by
        simp [Gval, t]
      have hqG : (⟨Gval z, hGmem z⟩ : X).1 v < 1 := by
        change Gval z v < 1
        rw [hGv]
        dsimp [t]
        linarith [hz]
      have hpG : (⟨Gval z, hGmem z⟩ : X) = G z := rfl
      have hdG : d (G z) = ydir z := by
        have hpunc : (⟨(G z).1, (G z).2.1, (G z).2.2, hqG⟩ :
            {x : V → ℝ // x ∈ (realization K).space ∧
              0 < x v ∧ x v < 1}) = q := by
          apply Subtype.ext
          simpa [G] using hqcoords.symm
        change (if h : (G z).1 v < 1 then
          (e ⟨(G z).1, (G z).2.1, (G z).2.2, h⟩).2 else y0) = ydir z
        rw [dif_pos hqG]
        have hEq := congrArg (fun a : {x : V → ℝ // x ∈ (realization K).space ∧
            0 < x v ∧ x v < 1} => (e a).2) hpunc
        rw [hEq, hq]
      have hrestore : eLink (ydir z) = dir z hz := by
        have hyd : ydir z = eLink.symm (dir z hz) := by
          change (if h : 0 < ‖z.1‖ then eLink.symm (dir z h) else y0) = _
          rw [dif_pos hz]
        rw [hyd]
        exact eLink.apply_symm_apply _
      change (1 - (G z).1 v) • (eLink (d (G z))).1 = z.1
      rw [hdG, hrestore]
      change (1 - Gval z v) • (dir z hz).1 = z.1
      rw [hGv]
      have hrad : 1 - t = ‖z.1‖ := by
        dsimp [t]
        ring
      have hdirValue : (dir z hz).1 = (‖z.1‖)⁻¹ • z.1 := rfl
      rw [hdirValue, smul_smul, hrad]
      rw [mul_inv_cancel₀ (ne_of_gt hz), one_smul]
    · have hz0 : ‖z.1‖ = 0 := le_antisymm (le_of_not_gt hz) (norm_nonneg _)
      have hzvec : z.1 = 0 := norm_eq_zero.mp hz0
      have hgz : Gval z = barycentricVertex v := by
        funext w
        by_cases hw : w = v
        · subst w
          simp [Gval, hz0, barycentricVertex, Pi.single_apply]
        · simp [Gval, hw, hz0, barycentricVertex, Pi.single_apply]
      change (1 - Gval z v) • (eLink (d (G z))).1 = z.1
      rw [hgz]
      have hcoord : barycentricVertex v v = 1 := by simp [barycentricVertex]
      rw [hcoord]
      simp only [sub_self, zero_smul]
      exact hzvec.symm
  exact ⟨Homeomorph.mk ⟨F, G, hGF, hFG⟩ hFcont hGcont⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.VertexStarBallChart
