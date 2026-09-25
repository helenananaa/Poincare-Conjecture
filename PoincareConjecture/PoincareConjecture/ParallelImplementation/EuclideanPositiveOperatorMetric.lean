import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.EuclideanPositiveOperatorMetric
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem exists_positive_operator_metric
    (A : E3 → (E3 →L[ℝ] E3)) (hA : ContDiff ℝ ∞ A)
    (hsym : ∀ (x v w : E3), inner ℝ (A x v) w = inner ℝ (A x w) v)
    (hpos : ∀ (x v : E3), v ≠ 0 → 0 < inner ℝ (A x v) v) :

    ∃ g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3,
      ∀ (x v w : E3), g.metricInner x v w = inner ℝ (A x v) w :=
/- SWARM_PROOF_BEGIN -/
by
  let toModel : ∀ x : E3, TangentSpace 𝓘(ℝ, E3) x →ₗ[ℝ] E3 := fun _ => {
    toFun := fun v => v
    map_add' := by intro v w; rfl
    map_smul' := by intro c v; rfl
  }
  let fromModel : ∀ x : E3, E3 →L[ℝ] TangentSpace 𝓘(ℝ, E3) x := fun _ => {
    toLinearMap := {
      toFun := fun v => v
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl
    }
    cont := by
      change Continuous (id : E3 → E3)
      exact continuous_id
  }
  have htoModel_cont (x : E3) : Continuous (toModel x) := by
    change Continuous (id : E3 → E3)
    exact continuous_id
  let core : ∀ x : E3, InnerProductSpace.Core ℝ (TangentSpace 𝓘(ℝ, E3) x) := fun x => {
    inner := fun v w => inner ℝ (toModel x v) (toModel x w)
    conj_inner_symm := by
      intro v w
      change inner ℝ (toModel x w) (toModel x v) = inner ℝ (toModel x v) (toModel x w)
      simp [real_inner_comm]
    re_inner_nonneg := by
      intro v
      change 0 ≤ inner ℝ (toModel x v) (toModel x v)
      rw [real_inner_self_eq_norm_sq]
      exact sq_nonneg _
    add_left := by
      intro v w z
      change inner ℝ (toModel x (v + w)) (toModel x z) = _
      rw [(toModel x).map_add, inner_add_left]
    smul_left := by
      intro v w c
      change inner ℝ (toModel x (c • v)) (toModel x w) = _
      rw [(toModel x).map_smul, inner_smul_left]
    definite := by
      intro v hv
      have hsq : ‖toModel x v‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq]
        exact hv
      have hnorm : ‖toModel x v‖ = 0 := by
        nlinarith [sq_nonneg (‖toModel x v‖)]
      have hv' : toModel x v = 0 := norm_eq_zero.mp hnorm
      simpa [toModel] using hv'
  }
  have hcore_cont (x : E3) :
      ContinuousAt (fun v : TangentSpace 𝓘(ℝ, E3) x => (core x).inner v v) 0 := by
    have hcont : Continuous
        (fun v : TangentSpace 𝓘(ℝ, E3) x => inner ℝ (toModel x v) (toModel x v)) := by
      fun_prop
    exact hcont.continuousAt
  have hcore_bounded (x : E3) :
      Bornology.IsVonNBounded ℝ {v : TangentSpace 𝓘(ℝ, E3) x |
        RCLike.re ((core x).inner v v) < 1} := by
    have hball : Bornology.IsVonNBounded ℝ (Metric.ball (0 : E3) 1) :=
      NormedSpace.isVonNBounded_ball ℝ E3 1
    have himage : (fromModel x) '' Metric.ball (0 : E3) 1 =
        {v : TangentSpace 𝓘(ℝ, E3) x | RCLike.re ((core x).inner v v) < 1} := by
      ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        have hu_norm : ‖u‖ < 1 := by simpa [Metric.mem_ball] using hu
        have hq : inner ℝ u u < 1 := by
          rw [real_inner_self_eq_norm_sq]
          nlinarith [norm_nonneg u]
        change RCLike.re (inner ℝ (toModel x (fromModel x u))
          (toModel x (fromModel x u))) < 1
        have htm : toModel x (fromModel x u) = u := rfl
        simpa [htm] using hq
      · intro hv
        have hq : inner ℝ (toModel x v) (toModel x v) < 1 := by
          change RCLike.re (inner ℝ (toModel x v) (toModel x v)) < 1 at hv
          simpa using hv
        refine ⟨toModel x v, ?_, ?_⟩
        · have hnorm : ‖toModel x v‖ < 1 := by
            have hsquare : ‖toModel x v‖ ^ 2 < 1 := by
              have := hq
              rw [real_inner_self_eq_norm_sq] at this
              exact this
            nlinarith [norm_nonneg (toModel x v)]
          simpa [Metric.mem_ball] using hnorm
        · change fromModel x (toModel x v) = v
          rfl
    rw [← himage]
    exact hball.image (fromModel x)
  letI : ∀ x : E3, NormedAddCommGroup (TangentSpace 𝓘(ℝ, E3) x) := fun x =>
    (core x).toNormedAddCommGroupOfTopology (hcore_cont x) (hcore_bounded x)
  letI : ∀ x : E3, NormedSpace ℝ (TangentSpace 𝓘(ℝ, E3) x) := fun x =>
    (core x).toNormedSpaceOfTopology (hcore_cont x) (hcore_bounded x)
  letI : ∀ x : E3, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E3) x) := fun x =>
    InnerProductSpace.ofCoreOfTopology (core x) (hcore_cont x) (hcore_bounded x)
  let e : ∀ x : E3, TangentSpace 𝓘(ℝ, E3) x ≃L[ℝ] E3 :=
    fun x => NormedSpace.fromTangentSpace x
  let post : (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3 →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ E3 E3 (E3 →L[ℝ] ℝ)
      (innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ)
  let B : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ := fun x => post (A x)
  let Btan : ∀ x : E3,
      TangentSpace 𝓘(ℝ, E3) x →L[ℝ] TangentSpace 𝓘(ℝ, E3) x →L[ℝ] ℝ :=
    fun x => (e x).symm.arrowCongr
      ((e x).symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (B x)
  have hB : ContDiff ℝ ∞ B := by
    exact ContDiff.continuousLinearMap_comp post (by simpa [B, post] using hA)
  have hB_apply (x v w : E3) : B x v w = inner ℝ (A x v) w := by
    simp only [B, post, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
    exact innerSL_apply_apply ℝ (A x v) w
  have hBtan_apply (x : E3) (v w : TangentSpace 𝓘(ℝ, E3) x) :
      Btan x v w = inner ℝ (A x (e x v)) (e x w) := by
    simp [Btan, B, post, e,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
      NormedSpace.fromTangentSpace, ContinuousLinearMap.id_apply]
    exact innerSL_apply_apply ℝ (A x v) w
  haveI : ProperSpace E3 := FiniteDimensional.proper_rclike ℝ E3
  let g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3 := {
    inner := Btan
    symm := by
      intro x v w
      rw [hBtan_apply, hBtan_apply]
      exact hsym x (e x v) (e x w)
    pos := by
      intro x v hv
      rw [hBtan_apply]
      have hv' : e x v ≠ 0 := by
        intro h
        apply hv
        apply (e x).injective
        simpa [h]
      exact hpos x (e x v) hv'
    isVonNBounded := by
      intro x
      let q : E3 → ℝ := fun v => inner ℝ (A x v) v
      have hqcont : Continuous q := by
        dsimp [q]
        fun_prop
      have hsphere : IsCompact (Metric.sphere (0 : E3) 1) := isCompact_sphere _ _
      obtain ⟨z, hz, hzmin⟩ := hsphere.exists_isMinOn
        (by
          obtain ⟨v, hv⟩ := exists_ne (0 : E3)
          refine ⟨‖v‖⁻¹ • v, ?_⟩
          have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
          simp [Metric.mem_sphere, dist_zero_right, norm_smul, abs_of_pos hvn, hvn.ne'])
        hqcont.continuousOn
      have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
      have hz0 : z ≠ 0 := by
        intro hz0
        have : ‖z‖ = 0 := by simpa using congrArg norm hz0
        rw [hznorm] at this
        norm_num at this
      have hqz : 0 < q z := by
        dsimp [q]
        exact hpos x z hz0
      have hqsmul (r : ℝ) (v : E3) : q (r • v) = r ^ 2 * q v := by
        dsimp [q]
        rw [map_smul, inner_smul_left, inner_smul_right]
        simp only [starRingEnd_apply, TrivialStar.star_trivial]
        ring
      have hnorm_bound : ∃ C : ℝ, ∀ v : E3, q v < 1 → ‖v‖ ≤ C := by
        refine ⟨(q z)⁻¹ + 1, fun v hv => ?_⟩
        by_cases hv0 : v = 0
        · subst v
          simp
          positivity
        have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
        let w : E3 := ‖v‖⁻¹ • v
        have hw : w ∈ Metric.sphere (0 : E3) 1 := by
          have hw_norm : ‖w‖ = 1 := by
            dsimp [w]
            rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hvn]
            exact (inv_mul_cancel₀ hvn.ne').trans (by norm_num)
          simpa [Metric.mem_sphere] using hw_norm
        have hzmin' : ∀ y ∈ Metric.sphere (0 : E3) 1, q z ≤ q y := by
          simpa [IsMinOn, IsMinFilter] using hzmin
        have hwmin : q z ≤ q w := hzmin' w hw
        have hv_eq : v = ‖v‖ • w := by
          dsimp [w]
          rw [smul_smul, mul_inv_cancel₀ hvn.ne', one_smul]
        have hqv : q v = ‖v‖ ^ 2 * q w := by
          calc
            q v = q (‖v‖ • w) := congrArg q hv_eq
            _ = ‖v‖ ^ 2 * q w := hqsmul _ _
        have hprod : q z * ‖v‖ ^ 2 < 1 := by
          calc
            q z * ‖v‖ ^ 2 = ‖v‖ ^ 2 * q z := by ring
            _ ≤ ‖v‖ ^ 2 * q w :=
              mul_le_mul_of_nonneg_left hwmin (sq_nonneg _)
            _ = q v := hqv.symm
            _ < 1 := hv
        have hsq : ‖v‖ ^ 2 ≤ (q z)⁻¹ := by
          rw [← one_div]
          apply (le_div_iff₀ hqz).2
          nlinarith [le_of_lt hprod]
        by_cases hle : ‖v‖ ≤ 1
        · exact hle.trans (by linarith [inv_pos.mpr hqz])
        · have hgt : 1 < ‖v‖ := lt_of_not_ge hle
          have hnorm_le_sq : ‖v‖ ≤ ‖v‖ ^ 2 := by nlinarith [sq_nonneg (‖v‖ - 1)]
          exact (hnorm_le_sq.trans hsq).trans (by linarith [inv_pos.mpr hqz])
      rcases hnorm_bound with ⟨C, hC⟩
      have hbnd : Bornology.IsBounded
          {v : TangentSpace 𝓘(ℝ, E3) x | Btan x v v < 1} := by
        rw [isBounded_iff_forall_norm_le]
        refine ⟨C, ?_⟩
        intro v hv
        have hv' : q (e x v) < 1 := by
          simpa [q, hBtan_apply] using hv
        have hnorm : ‖v‖ = ‖e x v‖ := by
          rw [norm_eq_sqrt_re_inner (𝕜 := ℝ) v,
            norm_eq_sqrt_re_inner (𝕜 := ℝ) (e x v)]
          congr 1
        rw [hnorm]
        exact hC (e x v) hv'
      exact NormedSpace.isVonNBounded_of_isBounded ℝ hbnd
    contMDiff := by
      intro x
      rw [Bundle.contMDiffAt_section]
      apply (contMDiffAt_iff_contDiffAt).2
      convert hB.contDiffAt using 1
      ext y v w
      simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        ContinuousLinearMap.comp_apply, Btan, B, post, e,
        NormedSpace.fromTangentSpace, TangentSpace]
  }
  refine ⟨g, ?_⟩
  intro x v w
  rw [Riemannian.RiemannianMetric.metricInner, hBtan_apply]
  simp [e, NormedSpace.fromTangentSpace]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.EuclideanPositiveOperatorMetric
