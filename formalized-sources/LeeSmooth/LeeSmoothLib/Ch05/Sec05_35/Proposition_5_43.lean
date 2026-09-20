import Mathlib
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_2
-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: the session did not provide `lean_leansearch`, so this statement uses the
-- chapter's verified `SmoothManifoldWithBoundary` owner and packages the defining-function
-- conditions in a local proof-only class to keep the proposition atomic.

open Set Function Filter
open scoped ContDiff Manifold Topology

noncomputable section

section

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [SmoothManifoldWithBoundary (n + 1) M]

/-- A boundary defining function is a smooth nonnegative real-valued function whose zero set is the
manifold boundary and whose manifold derivative is nonzero at every boundary point. -/
class IsBoundaryDefiningFunction (f : M → ℝ) : Prop where
  /-- The function is smooth as a map from the manifold with boundary to `ℝ`. -/
  contMDiff : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ f
  /-- The function is nonnegative everywhere on the manifold. -/
  nonneg : ∀ x : M, 0 ≤ f x
  /-- The zero set of the function is exactly the boundary of the manifold. -/
  zero_preimage :
    f ⁻¹' {0} = {p : M | (𝓡∂ (n + 1)).IsBoundaryPoint p}
  /-- The manifold derivative is nonzero at every boundary point. -/
  mfderiv_ne_zero :
    ∀ p : M, (𝓡∂ (n + 1)).IsBoundaryPoint p →
      mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f p ≠ 0

/-- The distinguished half-space coordinate, as a continuous linear map. -/
private def coord0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin (n + 1) ↦ ℝ) (0 : Fin (n + 1))

private lemma coord0_apply (y : EuclideanSpace ℝ (Fin (n + 1))) :
    coord0 (n := n) y = y 0 :=
  rfl

/-- Extended-chart images always lie in the model half-space, so the distinguished coordinate is
nonnegative everywhere. -/
private lemma extChartAt_coord0_nonneg (i x : M) :
    0 ≤ extChartAt (𝓡∂ (n + 1)) i x 0 := by
  have hxRange : extChartAt (𝓡∂ (n + 1)) i x ∈ range (𝓡∂ (n + 1)) := mem_range_self _
  simpa [range_modelWithCornersEuclideanHalfSpace] using hxRange

private lemma hasMFDerivAt_finset_sum {ι : Type*} {p : M} {t : Finset ι}
    (F : ι → M → ℝ) (F' : ι → (TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ))
    (h : ∀ i ∈ t, HasMFDerivAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (F i) p (F' i)) :
    HasMFDerivAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (fun x => ∑ i ∈ t, F i x) p (∑ i ∈ t, F' i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact hasMFDerivAt_const (0 : ℝ) p
  | insert i s hi ih =>
      have hfun :
          (fun x => ∑ j ∈ insert i s, F j x) =
            F i + fun x => ∑ j ∈ s, F j x := by
        ext x
        simp [Finset.sum_insert hi]
      rw [hfun, Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Proposition 5.43: every smooth manifold with boundary admits a boundary defining function. -/
theorem exists_boundary_defining_function :
    ∃ f : M → ℝ, @IsBoundaryDefiningFunction n M _ _ f := by
  classical
  letI : IsManifold (𝓡∂ (n + 1)) ∞ M := IsManifold.of_le le_top
  haveI : LocallyCompactSpace (EuclideanHalfSpace (n + 1)) :=
    (𝓡∂ (n + 1)).locallyCompactSpace
  haveI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanHalfSpace (n + 1)) M
  letI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source (I := 𝓡∂ (n + 1)) M
  let g : M → M → ℝ := fun i x => extChartAt (𝓡∂ (n + 1)) i x 0
  let f : M → ℝ := fun x => ∑ᶠ i, ρ i x * g i x
  have hterm_nonneg (i x : M) : 0 ≤ ρ i x * g i x :=
    mul_nonneg (ρ.nonneg i x) (extChartAt_coord0_nonneg i x)
  have hcoord0 :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) ∞ (coord0 (n := n)) :=
    (coord0 (n := n)).contMDiff
  have hgOn (i : M) :
      ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ (g i)
        (chartAt (EuclideanHalfSpace (n + 1)) i).source := by
    have hEq : g i = coord0 (n := n) ∘ extChartAt (𝓡∂ (n + 1)) i := by
      funext x
      simp [g, coord0_apply]
    rw [hEq]
    exact hcoord0.comp_contMDiffOn (contMDiffOn_extChartAt (I := 𝓡∂ (n + 1)) (x := i))
  have hfSmooth : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ f := by
    simpa [f, g, smul_eq_mul] using
      hρ.contMDiff_finsum_smul (n := (⊤ : ℕ∞)) (g := g)
        (fun i => (chartAt (EuclideanHalfSpace (n + 1)) i).open_source) hgOn
  have hfNonneg : ∀ x, 0 ≤ f x := by
    intro x
    simpa [f, smul_eq_mul] using finsum_nonneg fun i => hterm_nonneg i x
  have hmem_source {i x : M} (hsup : x ∈ tsupport (ρ i)) :
      x ∈ (chartAt (EuclideanHalfSpace (n + 1)) i).source :=
    hρ i hsup
  have hcoord0_eq_zero_iff {i x : M}
      (hx : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) i).source) :
      g i x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x := by
    have hchart :
        chartAt (EuclideanHalfSpace (n + 1)) i ∈
          atlas (EuclideanHalfSpace (n + 1)) M :=
      chart_mem_atlas _ i
    constructor
    · intro h0
      rw [(𝓡∂ (n + 1)).isBoundaryPoint_iff_not_isInteriorPoint]
      intro hInt
      have hIntTarget :
          extChartAt (𝓡∂ (n + 1)) i x ∈
            interior (extChartAt (𝓡∂ (n + 1)) i).target :=
        ((𝓡∂ (n + 1)).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) hchart hx).1
          hInt
      have hIntRange :
          extChartAt (𝓡∂ (n + 1)) i x ∈ interior (range (𝓡∂ (n + 1))) :=
        (chartAt (EuclideanHalfSpace (n + 1)) i).interior_extend_target_subset_interior_range
          hIntTarget
      have hpos : 0 < g i x := by
        simpa [g, interior_range_modelWithCornersEuclideanHalfSpace] using hIntRange
      exact (ne_of_gt hpos) h0
    · intro hBd
      by_contra hne
      have hpos : 0 < g i x :=
        lt_of_le_of_ne (extChartAt_coord0_nonneg i x) (Ne.symm hne)
      have hIntRange :
          extChartAt (𝓡∂ (n + 1)) i x ∈ interior (range (𝓡∂ (n + 1))) := by
        simpa [g, interior_range_modelWithCornersEuclideanHalfSpace] using hpos
      have hy :
          chartAt (EuclideanHalfSpace (n + 1)) i x ∈
            (chartAt (EuclideanHalfSpace (n + 1)) i).target :=
        (chartAt (EuclideanHalfSpace (n + 1)) i).map_source hx
      have hIntTarget :
          extChartAt (𝓡∂ (n + 1)) i x ∈
            interior (extChartAt (𝓡∂ (n + 1)) i).target := by
        simpa [extChartAt, OpenPartialHomeomorph.extend_coe] using
          (chartAt (EuclideanHalfSpace (n + 1)) i).mem_interior_extend_target hy hIntRange
      have hInt : (𝓡∂ (n + 1)).IsInteriorPoint x :=
        ((𝓡∂ (n + 1)).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) hchart hx).2
          hIntTarget
      exact ((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint x).1 hInt hBd
  have hfZero : f ⁻¹' {0} = {p : M | (𝓡∂ (n + 1)).IsBoundaryPoint p} := by
    ext x
    constructor
    · intro hf0
      have hx0 : f x = 0 := by simpa using hf0
      obtain ⟨i, hiPos⟩ := ρ.exists_pos_of_mem (mem_univ x)
      have hiSup : x ∈ tsupport (ρ i) :=
        subset_closure (mem_support.2 (ne_of_gt hiPos))
      have hiSrc : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) i).source :=
        hmem_source hiSup
      have hsum :
          ∑ j ∈ ρ.finsupport x, ρ j x * g j x = f x := by
        simpa [f, smul_eq_mul] using
          (ρ.sum_finsupport_smul_eq_finsum (x₀ := x) (φ := g))
      have hterm0 : ρ i x * g i x = 0 := by
        have hiFin : i ∈ ρ.finsupport x := by
          simpa [ρ.mem_finsupport] using ne_of_gt hiPos
        have hnonneg : ∀ j ∈ ρ.finsupport x, 0 ≤ ρ j x * g j x :=
          fun j _ => hterm_nonneg j x
        have hsum0 : ∑ j ∈ ρ.finsupport x, ρ j x * g j x = 0 := by
          simpa [hsum] using hx0
        exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum0 i hiFin
      have hg0 : g i x = 0 :=
        (mul_eq_zero.1 hterm0).resolve_left (ne_of_gt hiPos)
      exact (hcoord0_eq_zero_iff hiSrc).1 hg0
    · intro hBd
      change f x = 0
      have hsum :
          ∑ j ∈ ρ.finsupport x, ρ j x * g j x = f x := by
        simpa [f, smul_eq_mul] using
          (ρ.sum_finsupport_smul_eq_finsum (x₀ := x) (φ := g))
      rw [← hsum]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hiSup : x ∈ tsupport (ρ i) :=
        subset_closure (by simpa [ρ.mem_finsupport] using hi)
      have hiSrc : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) i).source :=
        hmem_source hiSup
      simp [(hcoord0_eq_zero_iff hiSrc).2 hBd]
  have hfDeriv :
      ∀ p, (𝓡∂ (n + 1)).IsBoundaryPoint p →
        mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f p ≠ 0 := by
    intro p hpBd
    let y0 : EuclideanSpace ℝ (Fin (n + 1)) := extChartAt (𝓡∂ (n + 1)) p p
    have hy0 : y0 0 = 0 := by
      have hFront : y0 ∈ frontier (range (𝓡∂ (n + 1))) := hpBd
      have : y0 ∈ {y : EuclideanSpace ℝ (Fin (n + 1)) | 0 = y 0} := by
        simpa [frontier_range_modelWithCornersEuclideanHalfSpace] using hFront
      exact this.symm
    let e0 : EuclideanSpace ℝ (Fin (n + 1)) :=
      EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)
    have he0_apply : e0 0 = 1 := by simp [e0]
    have he0Tan : e0 ∈ posTangentConeAt (range (𝓡∂ (n + 1))) y0 := by
      refine mem_posTangentConeAt_of_frequently_mem ?_
      refine Filter.Eventually.frequently ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have hcoord : (y0 + t • e0) 0 = t := by simp [hy0, he0_apply]
      have : 0 ≤ (y0 + t • e0) 0 := by
        rw [hcoord]
        exact ht.le
      simpa [range_modelWithCornersEuclideanHalfSpace] using this
    have hhyper {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : v 0 = 0) :
        v ∈ posTangentConeAt (range (𝓡∂ (n + 1))) y0 := by
      refine mem_posTangentConeAt_of_frequently_mem ?_
      refine Filter.Eventually.frequently ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have hcoord : (y0 + t • v) 0 = 0 := by simp [hy0, hv]
      have : 0 ≤ (y0 + t • v) 0 := by simp [hcoord]
      simpa [range_modelWithCornersEuclideanHalfSpace] using this
    have hEv :
        (fun x => ∑ i ∈ ρ.fintsupport p, ρ i x * g i x) =ᶠ[𝓝 p] f := by
      filter_upwards [ρ.eventually_finsupport_subset p] with x hx
      have hsum :
          ∑ i ∈ ρ.finsupport x, ρ i x * g i x = f x := by
        simpa [f, smul_eq_mul] using
          (ρ.sum_finsupport_smul_eq_finsum (x₀ := x) (φ := g))
      have hsubset :
          ∑ i ∈ ρ.fintsupport p, ρ i x * g i x =
            ∑ i ∈ ρ.finsupport x, ρ i x * g i x :=
        (Finset.sum_subset hx fun i _ hnot => by
            have hρ0 : ρ i x = 0 := by
              simpa [ρ.mem_finsupport] using hnot
            simp [hρ0]).symm
      exact hsubset.trans hsum
    have hmdiff_g {i : M}
        (hiSrc : p ∈ (chartAt (EuclideanHalfSpace (n + 1)) i).source) :
        MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (g i) p :=
      ((hgOn i).contMDiffAt
          ((chartAt (EuclideanHalfSpace (n + 1)) i).open_source.mem_nhds hiSrc)).mdifferentiableAt
        (by simp)
    have hmdiff_ρ (i : M) :
        MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (fun x => (ρ i : M → ℝ) x) p :=
      (ρ i).contMDiff.mdifferentiableAt (by simp)
    have hg0 {i : M}
        (hiSrc : p ∈ (chartAt (EuclideanHalfSpace (n + 1)) i).source) :
        g i p = 0 :=
      (hcoord0_eq_zero_iff hiSrc).2 hpBd
    have hgi_e0_pos {i : M}
        (hiSrc : p ∈ (chartAt (EuclideanHalfSpace (n + 1)) i).source) :
        (0 : ℝ) <
          (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (g i) p :
            TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ) e0 := by
      let dgi : TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ :=
        mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (g i) p
      have hgi : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (g i) p :=
        hmdiff_g hiSrc
      have hHas : HasMFDerivAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (g i) p dgi :=
        hgi.hasMFDerivAt
      let u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
        writtenInExtChartAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) p (g i)
      have hFDeriv : HasFDerivWithinAt u dgi (range (𝓡∂ (n + 1))) y0 :=
        hHas.2
      have uy0 : u y0 = 0 := by
        change g i ((extChartAt (𝓡∂ (n + 1)) p).symm y0) = 0
        have hleft : (extChartAt (𝓡∂ (n + 1)) p).symm y0 = p :=
          (extChartAt (𝓡∂ (n + 1)) p).left_inv (mem_extChartAt_source p)
        rw [hleft]
        exact hg0 hiSrc
      have hMin : IsLocalMinOn u (range (𝓡∂ (n + 1))) y0 :=
        Filter.Eventually.of_forall fun z => by
          have : 0 ≤ u z := by
            change 0 ≤ g i ((extChartAt (𝓡∂ (n + 1)) p).symm z)
            exact extChartAt_coord0_nonneg _ _
          simpa [uy0]
      have hge : (0 : ℝ) ≤ dgi e0 :=
        hMin.hasFDerivWithinAt_nonneg hFDeriv he0Tan
      have hne : dgi e0 ≠ 0 := by
        intro hzero_e0
        have hform0 : dgi = 0 := by
          apply ContinuousLinearMap.ext
          intro v
          let vE : EuclideanSpace ℝ (Fin (n + 1)) := v
          let c : ℝ := vE 0
          let w : EuclideanSpace ℝ (Fin (n + 1)) := vE - c • e0
          have hw0 : w 0 = 0 := by simp [w, c, e0]
          have hvTan : w ∈ posTangentConeAt (range (𝓡∂ (n + 1))) y0 := hhyper hw0
          have hvNeg : -w ∈ posTangentConeAt (range (𝓡∂ (n + 1))) y0 := by
            refine hhyper ?_
            simp [w, c, e0]
          have htang : dgi w = 0 :=
            hMin.hasFDerivWithinAt_eq_zero hFDeriv hvTan hvNeg
          have hlin : dgi v = dgi w + c • dgi e0 := by
            let wT : TangentSpace (𝓡∂ (n + 1)) p := w
            let eT : TangentSpace (𝓡∂ (n + 1)) p := e0
            have hvw : v = wT + c • eT := by
              change vE = w + c • e0
              simp [w]
            rw [hvw, map_add, map_smul]
          simpa [htang, hzero_e0] using hlin
        have hEqg : g i = coord0 (n := n) ∘ extChartAt (𝓡∂ (n + 1)) i := by
          funext x
          simp [g, coord0_apply]
        have hproj :
            MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ)
              (coord0 (n := n)) (extChartAt (𝓡∂ (n + 1)) i p) :=
          (coord0 (n := n)).mdifferentiableAt
        have hExt :
            MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
              (extChartAt (𝓡∂ (n + 1)) i) p :=
          (hasMFDerivAt_extChartAt hiSrc).mdifferentiableAt
        let dχ :
            TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
          mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
            (extChartAt (𝓡∂ (n + 1)) i) p
        have hcomp : dgi = (coord0 (n := n)).comp dχ := by
          have hchain := mfderiv_comp (x := p) hproj hExt
          have hcoord :
              mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ)
                (coord0 (n := n)) (extChartAt (𝓡∂ (n + 1)) i p) =
                coord0 (n := n) :=
            ContinuousLinearMap.mfderiv_eq (coord0 (n := n))
          dsimp [dgi, dχ]
          rw [hEqg, hchain, hcoord]
          rfl
        have hSurj : Function.Surjective dχ := by
          have hHasExt :
              HasMFDerivAt (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
                (extChartAt (𝓡∂ (n + 1)) i) p
                (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
                  (chartAt (EuclideanHalfSpace (n + 1)) i) p) :=
            hasMFDerivAt_extChartAt (I := 𝓡∂ (n + 1)) (x := i) hiSrc
          have hEq : dχ =
              (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
                (chartAt (EuclideanHalfSpace (n + 1)) i) p :
                TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :=
            hHasExt.mfderiv
          rw [hEq]
          exact (mdifferentiable_chart (I := 𝓡∂ (n + 1)) i).mfderiv_surjective hiSrc
        obtain ⟨w, hw⟩ := hSurj e0
        have hformw : dgi w = (dχ w) 0 := by
          rw [hcomp]
          simp [coord0_apply]
        have : (0 : ℝ) = (1 : ℝ) := by
          simpa [hform0, hw, he0_apply] using hformw.symm
        exact zero_ne_one this
      exact lt_of_le_of_ne hge hne.symm
    let F : M → M → ℝ := fun i x => ρ i x * g i x
    let F' : M → (TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ) := fun i =>
      (ρ i p) • (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (g i) p :
        TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ)
    have hHasTerm {i : M} (hiT : i ∈ ρ.fintsupport p) :
        HasMFDerivAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (F i) p (F' i) := by
      have hiTs : p ∈ tsupport (ρ i) := (ρ.mem_fintsupport_iff p i).1 hiT
      have hiSrc : p ∈ (chartAt (EuclideanHalfSpace (n + 1)) i).source :=
        hmem_source hiTs
      let ρ' : TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ :=
        mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (fun x => (ρ i : M → ℝ) x) p
      let g' : TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ :=
        mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (g i) p
      have hμ : HasMFDerivAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ)
          ((fun x => (ρ i : M → ℝ) x) * g i) p (ρ i p • g' + g i p • ρ') :=
        (hmdiff_ρ i).hasMFDerivAt.mul (hmdiff_g hiSrc).hasMFDerivAt
      have hFeq : F i = (fun x => (ρ i : M → ℝ) x) * g i := rfl
      rw [hFeq]
      have hF' : F' i = ρ i p • g' := rfl
      simpa [hF', hg0 hiSrc] using hμ
    have hHasSum :
        HasMFDerivAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ)
          (fun x => ∑ i ∈ ρ.fintsupport p, F i x) p
          (∑ i ∈ ρ.fintsupport p, F' i) :=
      hasMFDerivAt_finset_sum (t := ρ.fintsupport p) F F' fun i hi => hHasTerm hi
    have hmfderiv_f :
        (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f p :
            TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ) =
          ∑ i ∈ ρ.fintsupport p, F' i := by
      have hEq : (fun x => ∑ i ∈ ρ.fintsupport p, F i x) =ᶠ[𝓝 p] f := by
        simpa [F] using hEv
      rw [← hEq.mfderiv_eq]
      exact hHasSum.mfderiv
    have hsum_apply :
        ((∑ i ∈ ρ.fintsupport p, F' i) :
            TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ) e0 =
          ∑ i ∈ ρ.fintsupport p, F' i e0 := by
      refine Finset.induction_on (ρ.fintsupport p) ?_ ?_
      · simp
      · intro i s hi ih
        simp [Finset.sum_insert hi, add_apply, ih]
    have happly :
        ((mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f p :
            TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ) e0) =
          ∑ i ∈ ρ.fintsupport p, F' i e0 := by
      rw [hmfderiv_f]
      exact hsum_apply
    have hpos :
        (0 : ℝ) <
          (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f p :
            TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ) e0 := by
      rw [happly]
      refine Finset.sum_pos' ?_ ?_
      · intro i hi
        have hiTs : p ∈ tsupport (ρ i) := (ρ.mem_fintsupport_iff p i).1 hi
        have hiSrc : p ∈ (chartAt (EuclideanHalfSpace (n + 1)) i).source :=
          hmem_source hiTs
        have hgi := le_of_lt (hgi_e0_pos hiSrc)
        dsimp [F']
        exact smul_nonneg (ρ.nonneg i p) hgi
      · obtain ⟨i, hiPos⟩ := ρ.exists_pos_of_mem (mem_univ p)
        have hiTs : p ∈ tsupport (ρ i) :=
          subset_closure (mem_support.2 (ne_of_gt hiPos))
        have hiFin : i ∈ ρ.fintsupport p := (ρ.mem_fintsupport_iff p i).2 hiTs
        refine ⟨i, hiFin, ?_⟩
        have hiSrc : p ∈ (chartAt (EuclideanHalfSpace (n + 1)) i).source :=
          hmem_source hiTs
        dsimp [F']
        exact smul_pos hiPos (hgi_e0_pos hiSrc)
    intro hf0
    have : (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f p :
        TangentSpace (𝓡∂ (n + 1)) p →L[ℝ] ℝ) e0 = 0 := by
      simp [hf0]
    exact (ne_of_gt hpos) this
  exact ⟨f,
    { contMDiff := hfSmooth
      nonneg := hfNonneg
      zero_preimage := hfZero
      mfderiv_ne_zero := hfDeriv }⟩

end
