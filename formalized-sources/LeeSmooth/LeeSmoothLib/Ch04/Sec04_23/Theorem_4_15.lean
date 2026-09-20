import Mathlib
import LeeSmoothLib.Ch01.Sec01_06.Theorem_1_46
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_12
-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; local precedents used:
-- `Theorem_4_12`, `Problem_4_1`, and nearby manifold-with-boundary files using `𝓡∂ n`.

noncomputable section

open Set
open scoped ContDiff Manifold

universe uM uN

section LocalImmersionBoundary

variable {m n : ℕ}
variable [NeZero m]
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace m) M]
  [IsManifold (𝓡∂ m) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "J_m" => 𝓡∂ m
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- The half-space normal form for an immersion sends a boundary-model point to the corresponding
ambient `m`-tuple followed by `0` in the remaining target coordinates. -/
def boundary_immersion_normal_form (m n : ℕ) [NeZero m] :
    EuclideanHalfSpace m → EuclideanSpace ℝ (Fin n) :=
  fun x ↦ rank_normal_form m n m x.1

/-- On a half-space point, the boundary immersion normal form is the rank-`m` Euclidean normal
form applied to the underlying ambient coordinate tuple. -/
theorem boundary_immersion_normal_form_apply (x : EuclideanHalfSpace m) :
    boundary_immersion_normal_form m n x = rank_normal_form m n m x.1 := rfl

/-- A local coordinate normal form for a map from a manifold with boundary to a boundaryless
manifold consists of a centered smooth boundary chart on the source and a centered smooth chart on
the target in which the coordinate representative agrees with a prescribed half-space model map. -/
structure BoundaryLocalCoordinateNormalFormAt (F : M → N) (p : M)
    (normalForm : EuclideanHalfSpace m → EuclideanSpace ℝ (Fin n)) where
  domChart : OpenPartialHomeomorph M (EuclideanHalfSpace m)
  codChart : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n))
  domChart_mem_maximalAtlas :
    domChart ∈ IsManifold.maximalAtlas J_m ∞ M
  codChart_mem_maximalAtlas :
    codChart ∈ IsManifold.maximalAtlas I_n ∞ N
  domChart_centered : p ∈ domChart.source ∧ domChart p = 0
  codChart_centered : F p ∈ codChart.source ∧ codChart (F p) = 0
  mapsTo : MapsTo F domChart.source codChart.source
  eqOn : EqOn (codChart ∘ F ∘ domChart.symm) normalForm domChart.target

namespace BoundaryLocalCoordinateNormalFormAt

/-- Any boundary local coordinate normal form carries the source chart domain into the target chart
domain. -/
theorem mapsTo_source {F : M → N} {p : M}
    {normalForm : EuclideanHalfSpace m → EuclideanSpace ℝ (Fin n)}
    (h : BoundaryLocalCoordinateNormalFormAt F p normalForm) :
    MapsTo F h.domChart.source h.codChart.source := h.mapsTo

end BoundaryLocalCoordinateNormalFormAt

namespace Theorem415BoundaryImmersion

/-- Postcomposition by a smooth model-space chart change preserves maximal-atlas membership. -/
theorem trans_mem_maximalAtlas_of_mem_groupoid
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    {I : ModelWithCorners ℝ E H} [IsManifold I ∞ X]
    {e : OpenPartialHomeomorph X H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ X)
    {chi : OpenPartialHomeomorph H H}
    (hchi : chi ∈ contDiffGroupoid ∞ I) :
    e.trans chi ∈ IsManifold.maximalAtlas I ∞ X := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  have he'max : e' ∈ IsManifold.maximalAtlas I ∞ X :=
    IsManifold.subset_maximalAtlas he'
  have hleft : e.symm.trans e' ∈ contDiffGroupoid ∞ I :=
    IsManifold.compatible_of_mem_maximalAtlas he he'max
  have hright : e'.symm.trans e ∈ contDiffGroupoid ∞ I :=
    IsManifold.compatible_of_mem_maximalAtlas he'max he
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ∞ I).trans ((contDiffGroupoid ∞ I).symm hchi) hleft
  · simpa [OpenPartialHomeomorph.trans_assoc] using
      (contDiffGroupoid ∞ I).trans hright hchi

/-- Translation by a vector tangent to the boundary hyperplane is a homeomorphism of the
Euclidean half-space. -/
noncomputable def boundaryParallelTranslationHomeomorph
    (c : EuclideanHalfSpace m) (hc : c.1 0 = 0) :
    EuclideanHalfSpace m ≃ₜ EuclideanHalfSpace m :=
  let h : EuclideanSpace ℝ (Fin m) ≃ₜ EuclideanSpace ℝ (Fin m) :=
    Homeomorph.addRight (-c.1)
  h.sets <| by
    ext x
    constructor <;> intro hx
    · change 0 ≤ (h x) 0
      simpa [h, hc] using! hx
    · change 0 ≤ x 0 + -c.1 0 at hx
      simpa [hc] using! hx

theorem boundaryParallelTranslationHomeomorph_apply_val
    (c : EuclideanHalfSpace m) (hc : c.1 0 = 0) (x : EuclideanHalfSpace m) :
    (boundaryParallelTranslationHomeomorph c hc x).1 = x.1 - c.1 := rfl

theorem boundaryParallelTranslationHomeomorph_symm_apply_val
    (c : EuclideanHalfSpace m) (hc : c.1 0 = 0) (x : EuclideanHalfSpace m) :
    ((boundaryParallelTranslationHomeomorph c hc).symm x).1 = x.1 + c.1 := by
  have h := congrArg Subtype.val ((boundaryParallelTranslationHomeomorph c hc).right_inv x)
  change ((boundaryParallelTranslationHomeomorph c hc)
      ((boundaryParallelTranslationHomeomorph c hc).symm x)).1 = x.1 at h
  rw [boundaryParallelTranslationHomeomorph_apply_val] at h
  simpa [sub_eq_add_neg, add_comm] using (sub_eq_iff_eq_add.mp h)

theorem boundaryParallelTranslation_mem_contDiffGroupoid
    (c : EuclideanHalfSpace m) (hc : c.1 0 = 0) :
    (boundaryParallelTranslationHomeomorph c hc).toOpenPartialHomeomorph ∈
      contDiffGroupoid ∞ (J_m) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · have hforward :
        ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin m) ↦ x - c.1) univ := by
      simpa [sub_eq_add_neg] using (contDiff_id.add contDiff_const).contDiffOn
    refine hforward.congr_mono ?_ inter_subset_left
    intro x hx
    rcases mem_range.1 hx.2 with ⟨y, rfl⟩
    simpa using! boundaryParallelTranslationHomeomorph_apply_val c hc y
  · have hreverse :
        ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin m) ↦ x + c.1) univ := by
      simpa using (contDiff_id.add contDiff_const).contDiffOn
    refine hreverse.congr_mono ?_ inter_subset_left
    intro x hx
    rcases mem_range.1 hx.2 with ⟨y, rfl⟩
    simpa using! boundaryParallelTranslationHomeomorph_symm_apply_val c hc y

/-- Smooth Euclidean translations are valid model-space chart changes. -/
theorem euclideanTranslation_mem_contDiffGroupoid
    (v : EuclideanSpace ℝ (Fin n)) :
    (Homeomorph.addRight v).toOpenPartialHomeomorph ∈ contDiffGroupoid ∞ I_n := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa [modelWithCornersSelf_coe, Homeomorph.addRight] using
      (contDiff_id.add contDiff_const).contDiffOn
  · simpa [modelWithCornersSelf_coe, Homeomorph.addRight] using
      (contDiff_id.add contDiff_const).contDiffOn

/-- Euclidean linear automorphisms are valid smooth chart changes. -/
theorem euclideanLinearEquiv_mem_contDiffGroupoid
    {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)} :
    L.toHomeomorph.toOpenPartialHomeomorph ∈ contDiffGroupoid ∞ I_n := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa [modelWithCornersSelf_coe] using L.contDiff.contDiffOn
  · simpa [modelWithCornersSelf_coe] using L.symm.contDiff.contDiffOn

/-- A maximal half-space chart takes a boundary point to the boundary hyperplane. -/
theorem chart_value_fst_eq_zero_of_mem_boundary {p : M}
    (hp : p ∈ (𝓡∂ m).boundary M)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace m)}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ m) ∞ M) (hpe : p ∈ e.source) :
    (e p).1 0 = 0 := by
  have hnotI : ¬ (𝓡∂ m).IsInteriorPoint p :=
    ((𝓡∂ m).isBoundaryPoint_iff_not_isInteriorPoint p).mp hp
  have htarget : e.extend (𝓡∂ m) p ∈ (e.extend (𝓡∂ m)).target :=
    (e.extend J_m).map_source (by rwa [e.extend_source])
  have hrange : e.extend (𝓡∂ m) p ∈ range (𝓡∂ m) :=
    e.extend_target_subset_range htarget
  have hnonneg : 0 ≤ (e.extend (𝓡∂ m) p) 0 := by
    rw [range_modelWithCornersEuclideanHalfSpace] at hrange
    exact hrange
  have hextend_zero : e.extend (𝓡∂ m) p 0 = 0 := by
    apply le_antisymm ?_ hnonneg
    by_contra hx
    have hpos : 0 < (e.extend (𝓡∂ m) p) 0 := not_le.mp hx
    have hinterior_range : e.extend (𝓡∂ m) p ∈ interior (range (𝓡∂ m)) := by
      rw [interior_range_modelWithCornersEuclideanHalfSpace]
      exact hpos
    have hinterior_target : e.extend (𝓡∂ m) p ∈ interior (e.extend (𝓡∂ m)).target :=
      e.mem_interior_extend_target (e.map_source hpe) hinterior_range
    have hpI : (𝓡∂ m).IsInteriorPoint p :=
      ((𝓡∂ m).isInteriorPoint_iff_of_mem_maximalAtlas (by simp) he hpe).2 hinterior_target
    exact hnotI hpI
  change ((𝓡∂ m) (e p)) 0 = 0
  simpa [OpenPartialHomeomorph.extend_coe] using hextend_zero

/-- Canonical splitting of the first `m` coordinates from the last `n-m` coordinates. -/
noncomputable def standardProductEquiv (hmn : m ≤ n) :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin (n - m))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) :=
  ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n - m)).symm).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hmn)))).toContinuousLinearEquiv

theorem cast_congrArg_Fin_eq_Fin_cast {a b : ℕ} (h : a = b) (x : Fin a) :
    (cast (congrArg Fin h) x : Fin b) = Fin.cast h x := by
  subst h
  rfl

theorem equiv_cast_symm_castAdd_eq_castAdd
    (hmn : m ≤ n) (i : Fin m) :
    (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hmn))).symm
      (Fin.cast (Nat.add_sub_of_le hmn) (Fin.castAdd (n - m) i)) =
      Fin.castAdd (n - m) i := by
  calc
    (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hmn))).symm
        (Fin.cast (Nat.add_sub_of_le hmn) (Fin.castAdd (n - m) i)) =
      Fin.cast (Nat.add_sub_of_le hmn).symm
        (Fin.cast (Nat.add_sub_of_le hmn) (Fin.castAdd (n - m) i)) := by
          simpa [Equiv.cast] using
            cast_congrArg_Fin_eq_Fin_cast (Nat.add_sub_of_le hmn).symm
              (Fin.cast (Nat.add_sub_of_le hmn) (Fin.castAdd (n - m) i))
    _ = Fin.castAdd (n - m) i :=
      (Fin.leftInverse_cast (Nat.add_sub_of_le hmn)) (Fin.castAdd (n - m) i)

theorem equiv_cast_symm_natAdd_eq_natAdd
    (hmn : m ≤ n) (i : Fin (n - m)) :
    (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hmn))).symm
      (Fin.cast (Nat.add_sub_of_le hmn) (Fin.natAdd m i)) = Fin.natAdd m i := by
  calc
    (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hmn))).symm
        (Fin.cast (Nat.add_sub_of_le hmn) (Fin.natAdd m i)) =
      Fin.cast (Nat.add_sub_of_le hmn).symm
        (Fin.cast (Nat.add_sub_of_le hmn) (Fin.natAdd m i)) := by
          simpa [Equiv.cast] using
            cast_congrArg_Fin_eq_Fin_cast (Nat.add_sub_of_le hmn).symm
              (Fin.cast (Nat.add_sub_of_le hmn) (Fin.natAdd m i))
    _ = Fin.natAdd m i :=
      (Fin.leftInverse_cast (Nat.add_sub_of_le hmn)) (Fin.natAdd m i)

/-- The canonical product equivalence sends `(z, 0)` to the literal rank-`m` inclusion. -/
theorem standardProductEquiv_apply_zero (hmn : m ≤ n)
    (z : EuclideanSpace ℝ (Fin m)) :
    standardProductEquiv hmn (z, (0 : EuclideanSpace ℝ (Fin (n - m)))) =
      rank_normal_form m n m z := by
  ext i
  rcases (Fin.rightInverse_cast (Nat.add_sub_of_le hmn)).surjective i with ⟨j, rfl⟩
  refine Fin.addCases ?_ ?_ j
  · intro j'
    simp only [standardProductEquiv, rank_normal_form,
      ContinuousLinearEquiv.trans_apply]
    simp [Equiv.piCongrLeft']
    rw [equiv_cast_symm_castAdd_eq_castAdd hmn j', finSumFinEquiv_symm_apply_castAdd]
  · intro j'
    simp only [standardProductEquiv, rank_normal_form,
      ContinuousLinearEquiv.trans_apply]
    simp [Equiv.piCongrLeft']
    rw [equiv_cast_symm_natAdd_eq_natAdd hmn j', finSumFinEquiv_symm_apply_natAdd]
    simp

end Theorem415BoundaryImmersion

/-- Theorem 4.15 (Local Immersion Theorem for Manifolds with Boundary): if `F : M → N` is a smooth
immersion, with `M` a smooth `m`-manifold with boundary and `N` a smooth `n`-manifold, then every
boundary point `p ∈ ∂M` admits a centered smooth boundary chart on `M` and a centered smooth
coordinate chart on `N` in which `F` is written as `(x¹, …, xᵐ) ↦ (x¹, …, xᵐ, 0, …, 0)`. -/
theorem smooth_immersion_boundary_local_inclusion_form {F : M → N}
    (hF : Manifold.IsImmersion J_m I_n ∞ F) {p : M} (hp : p ∈ (𝓡∂ m).boundary M) :
    ∃ h : BoundaryLocalCoordinateNormalFormAt F p (boundary_immersion_normal_form m n), True :=
  by
    let hAt := hF.isImmersionAt p
    let hComp := hAt.complement
    haveI : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin m) × hComp) :=
      FiniteDimensional.of_injective hAt.equiv.toLinearMap hAt.equiv.injective
    haveI : FiniteDimensional ℝ hComp :=
      FiniteDimensional.of_injective
        (LinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) hComp) LinearMap.inr_injective
    have hfin_prod :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin m) × hComp) = n := by
      calc
        Module.finrank ℝ (EuclideanSpace ℝ (Fin m) × hComp) =
            Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) :=
          hAt.equiv.toLinearEquiv.finrank_eq
        _ = n := by simpa using finrank_euclideanSpace_fin (α := ℝ) (ι := Fin n)
    have hmn : m ≤ n := by
      calc
        m ≤ m + Module.finrank ℝ hComp := Nat.le_add_right m _
        _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin m) × hComp) := by
          simpa using
            (Module.finrank_prod ℝ (EuclideanSpace ℝ (Fin m)) hComp).symm
        _ = n := hfin_prod
    have hfin_comp : Module.finrank ℝ hComp = n - m := by
      have hsum : m + Module.finrank ℝ hComp = n := by
        calc
          m + Module.finrank ℝ hComp =
              Module.finrank ℝ (EuclideanSpace ℝ (Fin m) × hComp) := by
            simpa using
              (Module.finrank_prod ℝ (EuclideanSpace ℝ (Fin m)) hComp).symm
          _ = n := hfin_prod
      omega
    have hfin_comp_eq :
        Module.finrank ℝ hComp =
          Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - m))) := by
      calc
        Module.finrank ℝ hComp = n - m := hfin_comp
        _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - m))) := by
          simpa using finrank_euclideanSpace_fin (α := ℝ) (ι := Fin (n - m))
    let compEquiv : hComp ≃L[ℝ] EuclideanSpace ℝ (Fin (n - m)) :=
      ContinuousLinearEquiv.ofFinrankEq hfin_comp_eq
    let rawDomChart := hAt.domChart
    let rawCodChart := hAt.codChart
    let c : EuclideanHalfSpace m := rawDomChart p
    have hc : c.1 0 = 0 := by
      exact Theorem415BoundaryImmersion.chart_value_fst_eq_zero_of_mem_boundary
        hp hAt.domChart_mem_maximalAtlas hAt.mem_domChart_source
    let τ := Theorem415BoundaryImmersion.boundaryParallelTranslationHomeomorph c hc
    let domChart := rawDomChart.trans τ.toOpenPartialHomeomorph
    let codTranslation := Homeomorph.addRight (-rawCodChart (F p))
    let centeredCodChart := rawCodChart.trans codTranslation.toOpenPartialHomeomorph
    let straightening :
        EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      hAt.equiv.symm.trans
        (((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin m))).prodCongr compEquiv).trans
          (Theorem415BoundaryImmersion.standardProductEquiv hmn))
    let codChart :=
      centeredCodChart.trans straightening.toHomeomorph.toOpenPartialHomeomorph
    have hp_dom : p ∈ domChart.source := by
      simpa [domChart, OpenPartialHomeomorph.trans_source] using hAt.mem_domChart_source
    have hdom_zero : domChart p = 0 := by
      apply EuclideanHalfSpace.ext
      change (τ c).1 = (0 : EuclideanHalfSpace m).1
      rw [Theorem415BoundaryImmersion.boundaryParallelTranslationHomeomorph_apply_val]
      change c.1 - c.1 = (0 : EuclideanSpace ℝ (Fin m))
      simp
    have hp_cod : F p ∈ codChart.source := by
      simpa [codChart, centeredCodChart, OpenPartialHomeomorph.trans_source] using
        hAt.mem_codChart_source
    have hcod_zero : codChart (F p) = 0 := by
      simp [codChart, centeredCodChart, codTranslation, OpenPartialHomeomorph.trans_apply,
        Homeomorph.addRight]
    have hdom_max : domChart ∈ IsManifold.maximalAtlas J_m ∞ M := by
      exact Theorem415BoundaryImmersion.trans_mem_maximalAtlas_of_mem_groupoid
        hAt.domChart_mem_maximalAtlas
        (Theorem415BoundaryImmersion.boundaryParallelTranslation_mem_contDiffGroupoid c hc)
    have hcentered_cod_max :
        centeredCodChart ∈ IsManifold.maximalAtlas I_n ∞ N := by
      exact Theorem415BoundaryImmersion.trans_mem_maximalAtlas_of_mem_groupoid
        hAt.codChart_mem_maximalAtlas
        (Theorem415BoundaryImmersion.euclideanTranslation_mem_contDiffGroupoid
          (-rawCodChart (F p)))
    have hcod_max : codChart ∈ IsManifold.maximalAtlas I_n ∞ N := by
      exact Theorem415BoundaryImmersion.trans_mem_maximalAtlas_of_mem_groupoid
        hcentered_cod_max
        (Theorem415BoundaryImmersion.euclideanLinearEquiv_mem_contDiffGroupoid
          (L := straightening))
    have hmaps : MapsTo F domChart.source codChart.source := by
      intro y hy
      have hy_raw : y ∈ rawDomChart.source := by
        simpa [domChart, OpenPartialHomeomorph.trans_source] using hy
      have hy_cod_raw : F y ∈ rawCodChart.source :=
        hAt.source_subset_preimage_source hy_raw
      simpa [codChart, centeredCodChart, OpenPartialHomeomorph.trans_source] using hy_cod_raw
    have hcoord :
        EqOn (codChart ∘ F ∘ domChart.symm)
          (boundary_immersion_normal_form m n) domChart.target := by
      intro z hz
      have hz_raw : τ.symm z ∈ rawDomChart.target := by
        simpa [domChart, OpenPartialHomeomorph.trans_target] using hz
      have hz_raw_ext :
          (τ.symm z).1 ∈ (rawDomChart.extend J_m).target := by
        rw [OpenPartialHomeomorph.extend_target']
        exact ⟨τ.symm z, hz_raw, rfl⟩
      have hdom_symm : domChart.symm z = rawDomChart.symm (τ.symm z) := by
        rfl
      have hmodel_symm_z : (J_m).symm ((τ.symm z).1) = τ.symm z := by
        apply EuclideanHalfSpace.ext
        have hzrange : (τ.symm z).1 ∈ range J_m := ⟨τ.symm z, rfl⟩
        change (J_m) ((J_m).symm ((τ.symm z).1)) = (τ.symm z).1
        exact (J_m).right_inv hzrange
      have hraw :
          rawCodChart (F (domChart.symm z)) =
            hAt.equiv ((τ.symm z).1, (0 : hComp)) := by
        rw [hdom_symm]
        simpa [rawDomChart, rawCodChart, Function.comp, OpenPartialHomeomorph.extend_coe,
          OpenPartialHomeomorph.extend_coe_symm, hmodel_symm_z] using
            hAt.writtenInCharts hz_raw_ext
      have hc_target : c ∈ rawDomChart.target := by
        exact rawDomChart.map_source hAt.mem_domChart_source
      have hc_target_ext : c.1 ∈ (rawDomChart.extend J_m).target := by
        rw [OpenPartialHomeomorph.extend_target']
        exact ⟨c, hc_target, rfl⟩
      have hmodel_symm_c : (J_m).symm c.1 = c := by
        apply EuclideanHalfSpace.ext
        have hcrange : c.1 ∈ range J_m := ⟨c, rfl⟩
        change (J_m) ((J_m).symm c.1) = c.1
        exact (J_m).right_inv hcrange
      have hbase :
          rawCodChart (F p) = hAt.equiv (c.1, (0 : hComp)) := by
        have hp_inv : rawDomChart.symm c = p := by
          exact rawDomChart.left_inv hAt.mem_domChart_source
        calc
          rawCodChart (F p) = rawCodChart (F (rawDomChart.symm c)) := by rw [hp_inv]
          _ = hAt.equiv (c.1, (0 : hComp)) := by
            simpa [rawDomChart, rawCodChart, Function.comp,
              OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
              hmodel_symm_c] using
                hAt.writtenInCharts hc_target_ext
      have hcentered :
          centeredCodChart (F (domChart.symm z)) =
            hAt.equiv (z.1, (0 : hComp)) := by
        calc
          centeredCodChart (F (domChart.symm z)) =
              rawCodChart (F (domChart.symm z)) - rawCodChart (F p) := by
            simp [centeredCodChart, codTranslation, OpenPartialHomeomorph.trans_apply,
              Homeomorph.addRight, sub_eq_add_neg]
          _ = hAt.equiv ((τ.symm z).1, (0 : hComp)) -
              hAt.equiv (c.1, (0 : hComp)) := by rw [hraw, hbase]
          _ = hAt.equiv
              (((τ.symm z).1, (0 : hComp)) - (c.1, (0 : hComp))) := by
            rw [hAt.equiv.map_sub]
          _ = hAt.equiv (z.1, (0 : hComp)) := by
            rw [Theorem415BoundaryImmersion.boundaryParallelTranslationHomeomorph_symm_apply_val]
            simp
      calc
        (codChart ∘ F ∘ domChart.symm) z =
            straightening (centeredCodChart (F (domChart.symm z))) := by
          rfl
        _ = straightening (hAt.equiv (z.1, (0 : hComp))) := by rw [hcentered]
        _ = Theorem415BoundaryImmersion.standardProductEquiv hmn
            (z.1, (0 : EuclideanSpace ℝ (Fin (n - m)))) := by
          simp [straightening]
          apply Prod.ext
          · change z.1 = z.1
            rfl
          · change compEquiv 0 = 0
            exact map_zero compEquiv
        _ = rank_normal_form m n m z.1 :=
          Theorem415BoundaryImmersion.standardProductEquiv_apply_zero hmn z.1
        _ = boundary_immersion_normal_form m n z := rfl
    refine ⟨⟨domChart, codChart, hdom_max, hcod_max, ⟨hp_dom, hdom_zero⟩,
      ⟨hp_cod, hcod_zero⟩, hmaps, hcoord⟩, trivial⟩

end LocalImmersionBoundary
