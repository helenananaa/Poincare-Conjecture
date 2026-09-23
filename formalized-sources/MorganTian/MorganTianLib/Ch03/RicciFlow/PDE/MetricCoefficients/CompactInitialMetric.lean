import DoCarmoLib.Riemannian.Metric.RiemannianMetric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
open scoped Manifold Bundle
/-- Construct an actual initial metric on a compact smooth three-manifold.
The existence of the smooth structure is an assumption here, not the smoothing theorem. -/
theorem compact_smooth_initial_metric (M : Type*) [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M] :
    Nonempty (Riemannian.RiemannianMetric (𝓡 3) M) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let V : M → Type _ :=
    fun x => TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := innerSL ℝ
  have hB_symm : ∀ u v : E3, B u v = B v u := by
    intro u v
    change @inner ℝ E3 _ u v = @inner ℝ E3 _ v u
    exact real_inner_comm _ _
  have hB_pos : ∀ u : E3, u ≠ 0 → 0 < B u u := by
    intro u hu
    change 0 < @inner ℝ E3 _ u u
    exact real_inner_self_pos.mpr hu
  have hB_nonneg : ∀ u : E3, 0 ≤ B u u := by
    intro u
    change 0 ≤ @inner ℝ E3 _ u u
    exact real_inner_self_nonneg
  have hB_quad (u : E3) : B u u = ‖u‖ ^ 2 := by
    change @inner ℝ E3 _ u u = _
    rw [real_inner_self_eq_norm_sq]
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source (𝓡 3) M
  let e (i : M) :=
    trivializationAt E3 (TangentSpace (𝓡 3) : M → Type _) i
  let localInner (i x : M) : V x :=
    if hx : x ∈ (e i).baseSet then
      ((e i).continuousLinearEquivAt ℝ x hx).symm.arrowCongr
        (((e i).continuousLinearEquivAt ℝ x hx).symm.arrowCongr
          (ContinuousLinearEquiv.refl ℝ ℝ)) B
    else 0
  have hlocal_apply (i x : M) (hx : x ∈ (e i).baseSet)
      (u v : TangentSpace (𝓡 3) x) :
      localInner i x u v =
        B ((e i).continuousLinearEquivAt ℝ x hx u)
          ((e i).continuousLinearEquivAt ℝ x hx v) := by
    simp only [localInner, dif_pos hx]
    rfl
  have hlocal_smooth (i : M) :
      ContMDiffOn (𝓡 3)
        ((𝓡 3).prod 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ)) ∞
        (fun x => Bundle.TotalSpace.mk' (E3 →L[ℝ] E3 →L[ℝ] ℝ) x (localInner i x))
        (chartAt E3 i).source := by
    set eT := trivializationAt E3 (TangentSpace (𝓡 3) : M → Type _) i with heT
    have hchart : eT.baseSet = (chartAt E3 i).source := by
      simp [eT, TangentBundle.trivializationAt_baseSet]
    have hbase :
        (trivializationAt (E3 →L[ℝ] E3 →L[ℝ] ℝ) V i).baseSet = eT.baseSet := by
      have htriv0 :
          (trivializationAt ℝ (Bundle.Trivial M ℝ) i) =
            Bundle.Trivial.trivialization M ℝ :=
        Bundle.Trivial.eq_trivialization M ℝ _
      change (trivializationAt (E3 →L[ℝ] E3 →L[ℝ] ℝ) V i).baseSet =
        (trivializationAt E3 (TangentSpace (𝓡 3) : M → Type _) i).baseSet
      simp only [hom_trivializationAt_baseSet, ← heT, htriv0,
        Bundle.Trivial.trivialization, Set.inter_univ, Set.inter_self]
    rw [← hchart, ← hbase, Bundle.Trivialization.contMDiffOn_section_baseSet_iff]
    refine (contMDiffOn_const (c := B)).congr ?_
    intro y hy
    rw [hbase] at hy
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
    simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply]
    have hy₂ :
        y ∈ (trivializationAt (E3 →L[ℝ] ℝ)
          (fun x => TangentSpace (𝓡 3) x →L[ℝ] ℝ) i).baseSet := by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hy, Set.mem_univ y⟩
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt (E3 →L[ℝ] ℝ)
        (fun x => TangentSpace (𝓡 3) x →L[ℝ] ℝ) i) hy₂]
    simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply, ← heT]
    have htriv :
        (trivializationAt ℝ (Bundle.Trivial M ℝ) i) =
          Bundle.Trivial.trivialization M ℝ :=
      Bundle.Trivial.eq_trivialization M ℝ _
    have hy' : y ∈ (e i).baseSet := by
      simpa [eT, e] using hy
    have hei : e i = eT := by
      simp [eT, e]
    simp only [htriv, Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_apply, hei, hlocal_apply i y hy',
      ← Bundle.Trivialization.symm_continuousLinearEquivAt_eq' eT hy,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  let inner : (x : M) → V x := fun x => ∑ᶠ i, (ρ i x) • localInner i x
  have hweighted (i : M) :
      ContMDiff (𝓡 3)
        ((𝓡 3).prod 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ)) ∞
        (fun x => Bundle.TotalSpace.mk' (E3 →L[ℝ] E3 →L[ℝ] ℝ) x
          ((ρ i x) • localInner i x)) := by
    refine ContMDiffOn.smul_section_of_tsupport
      ((ρ i).contMDiff.contMDiffOn) (chartAt E3 i).open_source (hρ i)
      (hlocal_smooth i)
  have hweighted_locallyFinite :
      LocallyFinite (fun i : M => {x : M | (ρ i x) • localInner i x ≠ 0}) := by
    apply ρ.locallyFinite.subset
    intro i x hx
    rw [support]
    rw [mem_setOf_eq] at hx ⊢
    exact left_ne_zero_of_smul hx
  have hinner_smooth :
      ContMDiff (𝓡 3)
        ((𝓡 3).prod 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ)) ∞
        (fun x => Bundle.TotalSpace.mk' (E3 →L[ℝ] E3 →L[ℝ] ℝ) x (inner x)) := by
    apply ContMDiff.finsum_section_of_locallyFinite hweighted_locallyFinite
    intro i
    simpa [inner] using hweighted i
  have inner_apply (x : M) (u v : TangentSpace (𝓡 3) x) :
      inner x u v = ∑ᶠ i, (ρ i x) * localInner i x u v := by
    change (∑ᶠ i, (ρ i x) • localInner i x) u v = _
    rw [← ρ.sum_finsupport_smul_eq_finsum (x₀ := x)
      (fun i _y => localInner i x)]
    simpa [smul_eq_mul] using
      (ρ.sum_finsupport_smul_eq_finsum (x₀ := x)
        (fun i _y => localInner i x u v))
  have hlocal_nonneg (i x : M) (v : TangentSpace (𝓡 3) x) :
      0 ≤ localInner i x v v := by
    by_cases hx : x ∈ (e i).baseSet
    · rw [hlocal_apply i x hx v v]
      exact hB_nonneg _
    · simp [localInner, hx]
  have hlocal_symm (i x : M) (v w : TangentSpace (𝓡 3) x) :
      localInner i x v w = localInner i x w v := by
    by_cases hx : x ∈ (e i).baseSet
    · rw [hlocal_apply i x hx v w, hlocal_apply i x hx w v]
      exact hB_symm _ _
    · simp [localInner, hx]
  have hlocal_pos (i x : M) (hx : x ∈ (e i).baseSet)
      (v : TangentSpace (𝓡 3) x) (hv : v ≠ 0) :
      0 < localInner i x v v := by
    rw [hlocal_apply i x hx v v]
    apply hB_pos
    intro hzero
    apply hv
    apply ((e i).continuousLinearEquivAt ℝ x hx).injective
    rw [map_zero]
    exact hzero
  have hfinite (x : M) (u v : TangentSpace (𝓡 3) x) :
      HasFiniteSupport (fun i : M => (ρ i x) * localInner i x u v) := by
    apply (ρ.locallyFinite.point_finite x).subset
    intro i hi
    rw [mem_support] at hi
    change x ∈ support (ρ i)
    rw [mem_support]
    exact left_ne_zero_of_mul hi
  have hsource_of_weight {x : M} {i : M} (hi : 0 < ρ i x) :
      x ∈ (e i).baseSet := by
    have hmem : x ∈ support (ρ i) := by
      rw [mem_support]
      exact ne_of_gt hi
    have hts : x ∈ tsupport (ρ i) := subset_tsupport _ hmem
    have hsrc : x ∈ (chartAt E3 i).source := hρ i hts
    simpa [e, TangentBundle.trivializationAt_baseSet] using hsrc
  have hinner_symm (x : M) (u v : TangentSpace (𝓡 3) x) :
      inner x u v = inner x v u := by
    rw [inner_apply, inner_apply]
    apply finsum_congr
    intro i
    rw [hlocal_symm]
  have hinner_nonneg (x : M) (v : TangentSpace (𝓡 3) x) :
      0 ≤ inner x v v := by
    rw [inner_apply]
    apply finsum_nonneg
    intro i
    exact mul_nonneg (ρ.nonneg i x) (hlocal_nonneg i x v)
  have hinner_pos (x : M) (v : TangentSpace (𝓡 3) x) (hv : v ≠ 0) :
      0 < inner x v v := by
    rw [inner_apply]
    apply finsum_pos
    · intro i
      exact mul_nonneg (ρ.nonneg i x) (hlocal_nonneg i x v)
    · obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem (Set.mem_univ x)
      refine ⟨i, ?_⟩
      exact mul_pos hi (hlocal_pos i x (hsource_of_weight hi) v hv)
    · exact hfinite x v v
  have hinner_bounded (x : M) :
      Bornology.IsVonNBounded ℝ {v : TangentSpace (𝓡 3) x | inner x v v < 1} := by
    obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem (Set.mem_univ x)
    have hx := hsource_of_weight hi
    let c : ℝ := ρ i x
    have hc : 0 < c := hi
    let F := (e i).continuousLinearEquivAt ℝ x hx
    let T : ℝ := 2 + c + c⁻¹
    have hterm_le (v : TangentSpace (𝓡 3) x) :
        c * localInner i x v v ≤ inner x v v := by
      let f : M → ℝ := fun j =>
        if j = i then c * localInner i x v v else 0
      have hf : HasFiniteSupport f := by
        apply (Set.finite_singleton i).subset
        intro j hj
        by_contra hji
        have hjne : j ≠ i := by simpa using hji
        simp [Function.mem_support, f, hjne] at hj
      have hsingle : ∑ᶠ j, f j = c * localInner i x v v := by
        rw [finsum_eq_single f i]
        · simp [f]
        · intro j hji
          simp [f, hji]
      have hle : ∑ᶠ j, f j ≤ ∑ᶠ j, ρ j x * localInner j x v v := by
        apply finsum_le_finsum' hf (hfinite x v v)
        intro j
        by_cases hji : j = i
        · subst j
          simp [f, c]
        · simp [f, hji, c]
          exact mul_nonneg (ρ.nonneg j x) (hlocal_nonneg j x v)
      rw [inner_apply]
      calc
        c * localInner i x v v = ∑ᶠ j, f j := hsingle.symm
        _ ≤ ∑ᶠ j, ρ j x * localInner j x v v := hle
    have hcoord_quad (v : TangentSpace (𝓡 3) x) :
        localInner i x v v = ‖F v‖ ^ 2 := by
      rw [hlocal_apply i x hx v v]
      exact hB_quad (F v)
    have hT : 1 < T := by
      have hinv : 0 < c⁻¹ := inv_pos.mpr hc
      dsimp [T]
      linarith
    have hct : 1 ≤ c * T := by
      dsimp [T]
      rw [mul_add, mul_add, mul_inv_cancel₀ hc.ne']
      nlinarith [sq_nonneg c]
    have hctsq : 1 < c * T ^ 2 := by
      have hctpos : 0 < c * T := lt_of_lt_of_le zero_lt_one hct
      calc
        1 ≤ c * T := hct
        _ < (c * T) * T := by
          simpa using mul_lt_mul_of_pos_left hT hctpos
        _ = c * T ^ 2 := by ring
    have hcoord_bound {v : TangentSpace (𝓡 3) x}
        (hv : inner x v v < 1) : ‖F v‖ < T := by
      have hineq : c * ‖F v‖ ^ 2 < 1 := by
        calc
          c * ‖F v‖ ^ 2 = c * localInner i x v v := by rw [hcoord_quad]
          _ ≤ inner x v v := hterm_le v
          _ < 1 := hv
      by_contra h
      have hTle : T ≤ ‖F v‖ := le_of_not_gt h
      have hsq : T ^ 2 ≤ ‖F v‖ ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hTle)
          (add_nonneg (norm_nonneg (F v)) (by linarith : 0 ≤ T))]
      have hle : c * T ^ 2 ≤ c * ‖F v‖ ^ 2 := mul_le_mul_of_nonneg_left hsq hc.le
      linarith
    have hsubset : {v : TangentSpace (𝓡 3) x | inner x v v < 1} ⊆
        F.symm.toContinuousLinearMap '' Metric.ball (0 : E3) T := by
      intro v hv
      refine ⟨F v, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right]
        exact hcoord_bound hv
      · simp
    exact ((NormedSpace.isVonNBounded_ball ℝ E3 T).image
      F.symm.toContinuousLinearMap).subset hsubset
  exact ⟨{
    inner := inner
    symm := hinner_symm
    pos := hinner_pos
    isVonNBounded := hinner_bounded
    contMDiff := hinner_smooth
  }⟩
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
