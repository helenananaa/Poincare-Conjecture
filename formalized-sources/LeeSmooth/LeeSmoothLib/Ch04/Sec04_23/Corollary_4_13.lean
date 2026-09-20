import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_12
-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; local precedents used:
-- `Manifold.HasConstantRank` from `Exercise_4_4` and the rank-theorem normal-form API in
-- `Theorem_4_12`.

open Set
open scoped ContDiff Manifold Topology

universe uM uN

section

variable {m n : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

namespace LinearCoordinateRepresentationAux

/-- The standard rank normal form, bundled as a continuous linear map. -/
private def rankNormalFormCLM (m n r : ℕ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun := rank_normal_form m n r
  map_add' := by
    intro x y
    ext i
    by_cases hri : i.1 < r
    · by_cases hmi : i.1 < m
      · simp [rank_normal_form, hri, hmi, PiLp.add_apply]
      · simp [rank_normal_form, hri, hmi, PiLp.add_apply]
    · simp [rank_normal_form, hri, PiLp.add_apply]
  map_smul' := by
    intro c x
    ext i
    by_cases hri : i.1 < r
    · by_cases hmi : i.1 < m
      · simp [rank_normal_form, hri, hmi, PiLp.smul_apply]
      · simp [rank_normal_form, hri, hmi, PiLp.smul_apply]
    · simp [rank_normal_form, hri, PiLp.smul_apply]
  cont := by
    have hcoord :
        Continuous fun x : EuclideanSpace ℝ (Fin m) ↦
          fun i : Fin n ↦
            if i.1 < r then
              if hmi : i.1 < m then x ⟨i.1, hmi⟩ else 0
            else 0 := by
      apply continuous_pi
      intro i
      by_cases hri : i.1 < r
      · by_cases hmi : i.1 < m
        · simpa [hri, hmi] using
            (PiLp.continuous_apply (p := 2) (β := fun _ : Fin m ↦ ℝ) ⟨i.1, hmi⟩)
        · simpa [hri, hmi] using (continuous_const : Continuous fun _ :
            EuclideanSpace ℝ (Fin m) ↦ (0 : ℝ))
      · simpa [hri] using (continuous_const : Continuous fun _ :
          EuclideanSpace ℝ (Fin m) ↦ (0 : ℝ))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp hcoord

/-- Composing a linear map on either side by linear equivalences preserves the dimension of its
range. -/
private lemma finrank_range_comp_equivs
    {E₀ E₁ E₂ E₃ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
    (A : E₁ →L[ℝ] E₂) (B : E₂ ≃L[ℝ] E₃) (C : E₀ ≃L[ℝ] E₁) :
    Module.finrank ℝ A.range =
      Module.finrank ℝ (B.toContinuousLinearMap.comp
        (A.comp C.toContinuousLinearMap)).range := by
  have hright :
      (A.comp C.toContinuousLinearMap).toLinearMap.range = A.toLinearMap.range := by
    exact LinearMap.range_comp_of_range_eq_top A.toLinearMap C.toLinearEquiv.range
  rw [show
    (B.toContinuousLinearMap.comp (A.comp C.toContinuousLinearMap)).toLinearMap.range =
      Submodule.map B.toLinearEquiv.toLinearMap
        (A.comp C.toContinuousLinearMap).toLinearMap.range by
          exact LinearMap.range_comp _ _]
  rw [hright]
  exact (B.toLinearEquiv.finrank_map_eq A.toLinearMap.range).symm

end LinearCoordinateRepresentationAux

open LinearCoordinateRepresentationAux

/-- A local linear coordinate representation of `F` at `p` consists of smooth source and target
charts around `p` and `F p` in which the coordinate representative of `F` agrees with a linear
map on the source chart target. -/
structure LinearCoordinateRepresentationAt (F : M → N) (p : M) where
  domChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m))
  codChart : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n))
  domChart_mem_maximalAtlas :
    domChart ∈ IsManifold.maximalAtlas I_m ∞ M
  codChart_mem_maximalAtlas :
    codChart ∈ IsManifold.maximalAtlas I_n ∞ N
  point_mem_dom : p ∈ domChart.source
  image_mem_cod : F p ∈ codChart.source
  linearMap : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)
  mapsTo : MapsTo F domChart.source codChart.source
  eqOn : EqOn (codChart ∘ F ∘ domChart.symm) linearMap domChart.target

namespace LinearCoordinateRepresentationAux

/-- Within a fixed linear coordinate representation, the manifold rank is the rank of the fixed
linear map at every point of the source chart. -/
private lemma rankAt_eq_finrank_linearMap {F : M → N}
    (hF : ContMDiff I_m I_n ∞ F) {p q : M}
    (h : @LinearCoordinateRepresentationAt m n M _ _ N _ _ F p)
    (hq : q ∈ h.domChart.source) :
    Manifold.rankAt I_m I_n F q = Module.finrank ℝ h.linearMap.range := by
  let x : EuclideanSpace ℝ (Fin m) := h.domChart q
  have hx : x ∈ h.domChart.target := h.domChart.map_source hq
  have hxinv : h.domChart.symm x = q := h.domChart.left_inv hq
  have hFqcod : F q ∈ h.codChart.source := h.mapsTo hq
  have hFxcod : F (h.domChart.symm x) ∈ h.codChart.source := by
    simpa [hxinv] using hFqcod
  have hdomMD : h.domChart.MDifferentiable I_m I_m := by
    constructor
    · exact
        (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
          (by simp)
    · exact
        (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
          (by simp)
  have hcodMD : h.codChart.MDifferentiable I_n I_n := by
    constructor
    · exact
        (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mdifferentiableOn
          (by simp)
    · exact
        (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mdifferentiableOn
          (by simp)
  have hdomDiff : MDifferentiableAt I_m I_m h.domChart.symm x :=
    hdomMD.symm.mdifferentiableAt hx
  have hFDiff : MDifferentiableAt I_m I_n F (h.domChart.symm x) :=
    hF.mdifferentiableAt (by simp)
  have hcodDiff : MDifferentiableAt I_n I_n h.codChart (F (h.domChart.symm x)) :=
    hcodMD.mdifferentiableAt hFxcod
  have hcomp₁ :
      mfderiv I_m I_n (F ∘ h.domChart.symm) x =
        (mfderiv I_m I_n F (h.domChart.symm x)).comp
          (mfderiv I_m I_m h.domChart.symm x) :=
    mfderiv_comp x hFDiff hdomDiff
  have hcomp₂ :
      mfderiv I_m I_n (h.codChart ∘ (F ∘ h.domChart.symm)) x =
        (mfderiv I_n I_n h.codChart (F (h.domChart.symm x))).comp
          ((mfderiv I_m I_n F (h.domChart.symm x)).comp
            (mfderiv I_m I_m h.domChart.symm x)) := by
    rw [← hcomp₁]
    exact mfderiv_comp x hcodDiff (hFDiff.comp x hdomDiff)
  have hevent :
      (h.codChart ∘ F ∘ h.domChart.symm) =ᶠ[𝓝 x] h.linearMap := by
    filter_upwards [h.domChart.open_target.mem_nhds hx] with y hy
    exact h.eqOn hy
  have hrepDeriv :
      mfderiv I_m I_n (h.codChart ∘ F ∘ h.domChart.symm) x = h.linearMap := by
    calc
      mfderiv I_m I_n (h.codChart ∘ F ∘ h.domChart.symm) x =
          mfderiv I_m I_n h.linearMap x := hevent.mfderiv_eq
      _ = h.linearMap := h.linearMap.mfderiv_eq
  have hcoord :
      (hcodMD.mfderiv hFxcod).toContinuousLinearMap.comp
          ((mfderiv I_m I_n F (h.domChart.symm x)).comp
            (hdomMD.symm.mfderiv hx).toContinuousLinearMap) =
        h.linearMap := by
    change
      (mfderiv I_n I_n h.codChart (F (h.domChart.symm x))).comp
          ((mfderiv I_m I_n F (h.domChart.symm x)).comp
            (mfderiv I_m I_m h.domChart.symm x)) =
        h.linearMap
    rw [← hcomp₂]
    simpa [Function.comp_def] using hrepDeriv
  have hfin :=
    finrank_range_comp_equivs
      (E₀ := EuclideanSpace ℝ (Fin m))
      (E₁ := EuclideanSpace ℝ (Fin m))
      (E₂ := EuclideanSpace ℝ (Fin n))
      (E₃ := EuclideanSpace ℝ (Fin n))
      (mfderiv I_m I_n F (h.domChart.symm x))
      (hcodMD.mfderiv hFxcod)
      (hdomMD.symm.mfderiv hx)
  have hrankx :
      Manifold.rankAt I_m I_n F (h.domChart.symm x) =
        Module.finrank ℝ h.linearMap.range := by
    rw [Manifold.rankAt_eq_finrank_range_mfderiv]
    exact hfin.trans (congrArg (fun L : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin n) ↦ Module.finrank ℝ L.range) hcoord)
  simpa [hxinv] using hrankx

end LinearCoordinateRepresentationAux

variable [ConnectedSpace M]

/-- Corollary 4.13: for a smooth map on a connected smooth manifold, having a linear coordinate
representation near each point is equivalent to having constant rank. -/
theorem locally_linear_in_coordinates_iff_exists_constant_rank {F : M → N}
    (hF : ContMDiff I_m I_n ∞ F) :
    (∀ p : M, Nonempty (@LinearCoordinateRepresentationAt m n M _ _ N _ _ F p)) ↔
      ∃ r : ℕ, Manifold.HasConstantRank I_m I_n F r := by
  constructor
  · intro hlinear
    have hlocal : IsLocallyConstant (Manifold.rankAt I_m I_n F) := by
      rw [IsLocallyConstant.iff_exists_open]
      intro p
      obtain ⟨linear⟩ := hlinear p
      refine ⟨linear.domChart.source, linear.domChart.open_source,
        linear.point_mem_dom, ?_⟩
      intro q hq
      exact
        (rankAt_eq_finrank_linearMap hF linear hq).trans
          (rankAt_eq_finrank_linearMap hF linear linear.point_mem_dom).symm
    let p : M := Classical.arbitrary M
    refine ⟨Manifold.rankAt I_m I_n F p, ?_, ?_⟩
    · exact hF.mdifferentiable (by simp)
    · intro q
      exact hlocal.apply_eq_of_preconnectedSpace q p
  · rintro ⟨r, hrank⟩ p
    obtain ⟨normal, -⟩ :=
      constant_rank_local_coordinate_normal_form hF hrank p
    exact ⟨{
      domChart := normal.domChart
      codChart := normal.codChart
      domChart_mem_maximalAtlas := normal.domChart_mem_maximalAtlas
      codChart_mem_maximalAtlas := normal.codChart_mem_maximalAtlas
      point_mem_dom := normal.domChart_centered.1
      image_mem_cod := normal.codChart_centered.1
      linearMap := rankNormalFormCLM m n r
      mapsTo := normal.mapsTo
      eqOn := by simpa [rankNormalFormCLM] using normal.eqOn }⟩

end
