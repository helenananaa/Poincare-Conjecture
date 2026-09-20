import Mathlib.Geometry.Manifold.LocalDiffeomorph
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5
import LeeSmoothLib.Ch05.Sec05_37.BoundaryRegularPreimageLinear
import LeeSmoothLib.Ch05.Sec05_37.BoundaryPreimageCharts
import LeeSmoothLib.Ch05.Sec05_37.CInfinityNeatSliceAtlas
import LeeSmoothLib.Ch05.Sec05_37.BoundaryRegularValueCore

/-!
# Pointwise boundary neat-slice chart for Problem 5-23

At a boundary fiber point whose derivative is surjective on the standard normal kernel, extend
the preferred chart representative of `F` by the public Seeley lemma, straighten by a
normal-preserving linear split, apply the ordinary inverse function theorem, and restrict to the
closed half-space.  The result is a single ambient maximal-atlas chart in which the fiber is the
zero-complement neat slice.  No chart family is assumed.
-/

open Set Function ChartedSpace IsManifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace Manifold.BoundaryRegularPreimageChart

universe uM uN

variable {n m : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold (𝓡 m) ∞ N]

local notation "I∂" => 𝓡∂ (n + 1)
local notation "Eₙ" => EuclideanSpace ℝ (Fin (n + 1))
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₖ" => EuclideanSpace ℝ (Fin ((n - m) + 1))

/-! ### Chart-domain geometry at a boundary point -/

theorem extChartAt_normal_eq_zero_of_mem_boundary {p : M}
    (hp : p ∈ (𝓡∂ (n + 1)).boundary M) :
    extChartAt (𝓡∂ (n + 1)) p p 0 = 0 := by
  have hp' : extChartAt (𝓡∂ (n + 1)) p p ∈ frontier (range (𝓡∂ (n + 1))) := hp
  rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hp'
  exact hp'.symm

theorem extChartAt_mem_range (p : M) :
    extChartAt (𝓡∂ (n + 1)) p p ∈ range (𝓡∂ (n + 1)) :=
  mem_range_self _

/-- An ordinary open Euclidean neighbourhood whose closed-half-space slice sits in the preferred
extended-chart domain of `F`. -/
theorem exists_open_nhd_subset_writtenInExtChartAt_domain
    {F : M → N} {p : M} (hF : ContMDiff (𝓡∂ (n + 1)) (𝓡 m) ∞ F) :
    ∃ W : Set Eₙ, IsOpen W ∧ extChartAt (𝓡∂ (n + 1)) p p ∈ W ∧
      W ∩ range (𝓡∂ (n + 1)) ⊆
        ((extChartAt (𝓡∂ (n + 1)) p).target ∩
          (F ∘ (extChartAt (𝓡∂ (n + 1)) p).symm) ⁻¹'
            (extChartAt (𝓡 m) (F p)).source) := by
  let a : Eₙ := extChartAt (𝓡∂ (n + 1)) p p
  have hTarget :
      (extChartAt (𝓡∂ (n + 1)) p).target ∪ (range (𝓡∂ (n + 1)))ᶜ ∈ 𝓝 a :=
    extChartAt_target_union_compl_range_mem_nhds_of_mem (mem_extChartAt_target p)
  have hFsrc : F ⁻¹' (extChartAt (𝓡 m) (F p)).source ∈ 𝓝 p :=
    hF.continuous.continuousAt.preimage_mem_nhds
      (isOpen_extChartAt_source (I := 𝓡 m) (F p) |>.mem_nhds
        (mem_extChartAt_source (I := 𝓡 m) (F p)))
  have hPre : (F ∘ (extChartAt (𝓡∂ (n + 1)) p).symm) ⁻¹'
      (extChartAt (𝓡 m) (F p)).source ∈ 𝓝 a := by
    have h : (extChartAt (𝓡∂ (n + 1)) p).symm ⁻¹'
        (F ⁻¹' (extChartAt (𝓡 m) (F p)).source) ∈ 𝓝 a := by
      simpa [a, extChartAt] using
        extChartAt_preimage_mem_nhds (I := 𝓡∂ (n + 1)) (x := p) hFsrc
    simpa [preimage_comp] using h
  rcases mem_nhds_iff.mp (Filter.inter_mem hTarget hPre) with ⟨W, hWsub, hWopen, haW⟩
  refine ⟨W, hWopen, haW, ?_⟩
  intro z hz
  have hzW : z ∈ W := hz.1
  have hzRange : z ∈ range (𝓡∂ (n + 1)) := hz.2
  have hzU : z ∈ (extChartAt (𝓡∂ (n + 1)) p).target ∪ (range (𝓡∂ (n + 1)))ᶜ ∧
      z ∈ (F ∘ (extChartAt (𝓡∂ (n + 1)) p).symm) ⁻¹'
        (extChartAt (𝓡 m) (F p)).source := hWsub hzW
  refine ⟨?_, hzU.2⟩
  rcases hzU.1 with hzT | hzCompl
  · exact hzT
  · exact (hzCompl hzRange).elim

/-! ### Seeley extension and uniqueDiff recovery of `mfderiv` -/

theorem fderiv_eqOn_halfSpace_eq_mfderiv
    {F : M → N} {p : M} {V : Set Eₙ} {Ftilde : Eₙ → Eₘ}
    (hF : ContMDiff (𝓡∂ (n + 1)) (𝓡 m) ∞ F)
    (hV : IsOpen V) (haV : extChartAt (𝓡∂ (n + 1)) p p ∈ V)
    (hEq : EqOn Ftilde (writtenInExtChartAt (𝓡∂ (n + 1)) (𝓡 m) p F)
      (V ∩ range (𝓡∂ (n + 1))))
    (hDiff : DifferentiableAt ℝ Ftilde (extChartAt (𝓡∂ (n + 1)) p p)) :
    fderiv ℝ Ftilde (extChartAt (𝓡∂ (n + 1)) p p) =
      mfderiv (𝓡∂ (n + 1)) (𝓡 m) F p := by
  let a : Eₙ := extChartAt (𝓡∂ (n + 1)) p p
  let fRep : Eₙ → Eₘ := writtenInExtChartAt (𝓡∂ (n + 1)) (𝓡 m) p F
  have hmd : MDifferentiableAt (𝓡∂ (n + 1)) (𝓡 m) F p :=
    hF.mdifferentiableAt (by simp)
  have hmf : mfderiv (𝓡∂ (n + 1)) (𝓡 m) F p =
      fderivWithin ℝ fRep (range (𝓡∂ (n + 1))) a :=
    hmd.mfderiv
  have hFtildeAt : HasFDerivAt Ftilde (fderiv ℝ Ftilde a) a :=
    hDiff.hasFDerivAt
  have hFtildeWithin : HasFDerivWithinAt Ftilde (fderiv ℝ Ftilde a)
      (range (𝓡∂ (n + 1))) a :=
    hFtildeAt.hasFDerivWithinAt
  have hEv : Ftilde =ᶠ[𝓝[range (𝓡∂ (n + 1))] a] fRep := by
    have hmem : V ∩ range (𝓡∂ (n + 1)) ∈ 𝓝[range (𝓡∂ (n + 1))] a := by
      rw [inter_comm]
      exact inter_mem_nhdsWithin (range (𝓡∂ (n + 1))) (hV.mem_nhds haV)
    exact hEq.eventuallyEq_of_mem hmem
  have haEq : Ftilde a = fRep a :=
    hEq ⟨haV, mem_range_self _⟩
  have hfRepWithin : HasFDerivWithinAt fRep (fderiv ℝ Ftilde a)
      (range (𝓡∂ (n + 1))) a :=
    hFtildeWithin.congr_of_eventuallyEq hEv.symm haEq.symm
  have huniq : UniqueDiffWithinAt ℝ (range (𝓡∂ (n + 1))) a :=
    (𝓡∂ (n + 1)).uniqueDiffOn a (mem_range_self _)
  have hfw : fderivWithin ℝ fRep (range (𝓡∂ (n + 1))) a = fderiv ℝ Ftilde a :=
    hfRepWithin.fderivWithin huniq
  exact hfw.symm.trans hmf.symm

/-! ### Normal-preserving straightening map -/

/-- Euclidean straightening used at a boundary fiber point:
`G(z) = L((L.symm(z-a)).1, Ftilde(z)-b)`.  The first free slot of `L` is the ambient
normal, so if `a 0 = 0` then `G(z) 0 = z 0`. -/
def boundaryStraighteningMap
    (L : (Eₖ × Eₘ) ≃L[ℝ] Eₙ) (a : Eₙ) (Ftilde : Eₙ → Eₘ) (b : Eₘ) :
    Eₙ → Eₙ :=
  fun z => L ((L.symm (z - a)).1, Ftilde z - b)

theorem boundaryStraighteningMap_apply_zero
    (L : (Eₖ × Eₘ) ≃L[ℝ] Eₙ)
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    (a : Eₙ) (ha0 : a 0 = 0) (Ftilde : Eₙ → Eₘ) (b : Eₘ) (z : Eₙ) :
    boundaryStraighteningMap (n := n) (m := m) L a Ftilde b z 0 = z 0 := by
  have hsymm0 : ∀ w : Eₙ, (L.symm w).1 0 = w 0 := by
    intro w
    have hw := hNormal (L.symm w).1 (L.symm w).2
    rw [L.apply_symm_apply] at hw
    exact hw.symm
  change (L ((L.symm (z - a)).1, Ftilde z - b)) 0 = z 0
  rw [hNormal, hsymm0]
  simp [ha0]

theorem boundaryStraighteningMap_linear_eq_id
    (L : (Eₖ × Eₘ) ≃L[ℝ] Eₙ)
    (A : Eₙ →L[ℝ] Eₘ) (hAL : ∀ w, A (L w) = w.2) :
    L.toContinuousLinearMap.comp
        (((ContinuousLinearMap.fst ℝ Eₖ Eₘ).comp L.symm.toContinuousLinearMap).prod A) =
      ContinuousLinearMap.id ℝ Eₙ := by
  apply ContinuousLinearMap.ext
  intro x
  change L ((L.symm x).1, A x) = x
  have hx : A x = (L.symm x).2 := by
    have h := hAL (L.symm x)
    rwa [L.apply_symm_apply] at h
  rw [hx, Prod.mk.eta, L.apply_symm_apply]

theorem hasFDerivAt_boundaryStraighteningMap
    (L : (Eₖ × Eₘ) ≃L[ℝ] Eₙ)
    {A : Eₙ →L[ℝ] Eₘ} {a : Eₙ} {Ftilde : Eₙ → Eₘ} {b : Eₘ}
    (hFtilde : HasFDerivAt Ftilde A a) :
    HasFDerivAt (boundaryStraighteningMap (n := n) (m := m) L a Ftilde b)
      (L.toContinuousLinearMap.comp
        (((ContinuousLinearMap.fst ℝ Eₖ Eₘ).comp L.symm.toContinuousLinearMap).prod A))
      a := by
  let free : Eₙ → Eₖ := fun z => (L.symm (z - a)).1
  let constraint : Eₙ → Eₘ := fun z => Ftilde z - b
  have hsub : HasFDerivAt (fun z : Eₙ => z - a) (ContinuousLinearMap.id ℝ Eₙ) a :=
    (hasFDerivAt_id a).sub_const a
  have hLsymm : HasFDerivAt (fun z : Eₙ => (L.symm (z - a) : Eₖ × Eₘ))
      L.symm.toContinuousLinearMap a :=
    L.symm.toContinuousLinearMap.hasFDerivAt.comp a hsub
  have hfree : HasFDerivAt free
      ((ContinuousLinearMap.fst ℝ Eₖ Eₘ).comp L.symm.toContinuousLinearMap) a :=
    (ContinuousLinearMap.fst ℝ Eₖ Eₘ).hasFDerivAt.comp a hLsymm
  have hconstraint : HasFDerivAt constraint A a :=
    hFtilde.sub_const b
  have hpair : HasFDerivAt (fun z : Eₙ => (free z, constraint z))
      (((ContinuousLinearMap.fst ℝ Eₖ Eₘ).comp L.symm.toContinuousLinearMap).prod A) a :=
    hfree.prodMk hconstraint
  have hG : HasFDerivAt (fun z : Eₙ => L (free z, constraint z))
      (L.toContinuousLinearMap.comp
        (((ContinuousLinearMap.fst ℝ Eₖ Eₘ).comp L.symm.toContinuousLinearMap).prod A)) a :=
    L.toContinuousLinearMap.hasFDerivAt.comp a hpair
  convert hG
  rfl

theorem fderiv_boundaryStraighteningMap_eq_id
    (L : (Eₖ × Eₘ) ≃L[ℝ] Eₙ)
    {A : Eₙ →L[ℝ] Eₘ} (hAL : ∀ w, A (L w) = w.2)
    {a : Eₙ} {Ftilde : Eₙ → Eₘ} {b : Eₘ}
    (hFtilde : HasFDerivAt Ftilde A a) :
    fderiv ℝ (boundaryStraighteningMap (n := n) (m := m) L a Ftilde b) a =
      ContinuousLinearMap.id ℝ Eₙ := by
  let dG : Eₙ →L[ℝ] Eₙ :=
    L.toContinuousLinearMap.comp
      (((ContinuousLinearMap.fst ℝ Eₖ Eₘ).comp L.symm.toContinuousLinearMap).prod A)
  have hG : HasFDerivAt (boundaryStraighteningMap (n := n) (m := m) L a Ftilde b) dG a :=
    hasFDerivAt_boundaryStraighteningMap (n := n) (m := m) (b := b) L hFtilde
  have hid : dG = ContinuousLinearMap.id ℝ Eₙ :=
    boundaryStraighteningMap_linear_eq_id (n := n) (m := m) L A hAL
  exact hG.fderiv.trans hid

theorem hasFDerivAt_boundaryStraighteningMap_id
    (L : (Eₖ × Eₘ) ≃L[ℝ] Eₙ)
    {A : Eₙ →L[ℝ] Eₘ} (hAL : ∀ w, A (L w) = w.2)
    {a : Eₙ} {Ftilde : Eₙ → Eₘ} {b : Eₘ}
    (hFtilde : HasFDerivAt Ftilde A a) :
    HasFDerivAt (boundaryStraighteningMap (n := n) (m := m) L a Ftilde b)
      (ContinuousLinearMap.id ℝ Eₙ) a := by
  have h := hasFDerivAt_boundaryStraighteningMap (n := n) (m := m) (b := b) L hFtilde
  rwa [boundaryStraighteningMap_linear_eq_id (n := n) (m := m) L A hAL] at h

theorem contDiffOn_boundaryStraighteningMap
    (L : (Eₖ × Eₘ) ≃L[ℝ] Eₙ) (a : Eₙ) {Ftilde : Eₙ → Eₘ} (b : Eₘ)
    {V : Set Eₙ} (hFtilde : ContDiffOn ℝ ∞ Ftilde V) :
    ContDiffOn ℝ ∞ (boundaryStraighteningMap (n := n) (m := m) L a Ftilde b) V := by
  have hfree : ContDiffOn ℝ ∞ (fun z : Eₙ => (L.symm (z - a)).1) V :=
    (contDiff_fst.comp L.symm.contDiff).comp (contDiff_id.sub contDiff_const) |>.contDiffOn
  have hconstraint : ContDiffOn ℝ ∞ (fun z : Eₙ => Ftilde z - b) V :=
    hFtilde.sub (contDiff_const (n := ∞) (c := b)).contDiffOn
  exact L.contDiff.comp_contDiffOn (hfree.prodMk hconstraint)

/-! ### Inverse-function-theorem branch preserving the normal -/

theorem exists_normal_preserving_ift_branch
    (L : (Eₖ × Eₘ) ≃L[ℝ] Eₙ)
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    {A : Eₙ →L[ℝ] Eₘ} (hAL : ∀ w, A (L w) = w.2)
    {a : Eₙ} (ha0 : a 0 = 0) {Ftilde : Eₙ → Eₘ} {b : Eₘ}
    {V : Set Eₙ} (hV : IsOpen V) (haV : a ∈ V)
    (hFtildeOn : ContDiffOn ℝ ∞ Ftilde V)
    (hFtildeAt : HasFDerivAt Ftilde A a) :
    ∃ Ψ : OpenPartialHomeomorph Eₙ Eₙ,
      a ∈ Ψ.source ∧ Ψ.source ⊆ V ∧
        (∀ z ∈ Ψ.source, Ψ z = boundaryStraighteningMap (n := n) (m := m) L a Ftilde b z) ∧
          (∀ z ∈ Ψ.source, Ψ z 0 = z 0) ∧
            (∀ z ∈ Ψ.target, Ψ.symm z 0 = z 0) ∧
              ContDiffOn ℝ ∞ (Ψ : Eₙ → Eₙ) Ψ.source ∧
                ContDiffOn ℝ ∞ Ψ.symm Ψ.target := by
  let G : Eₙ → Eₙ := boundaryStraighteningMap (n := n) (m := m) L a Ftilde b
  have hGOn : ContDiffOn ℝ ∞ G V :=
    contDiffOn_boundaryStraighteningMap (n := n) (m := m) L a b hFtildeOn
  have hGAt : ContDiffAt ℝ ∞ G a := hGOn.contDiffAt (hV.mem_nhds haV)
  have hGderiv : HasFDerivAt G (ContinuousLinearMap.id ℝ Eₙ) a :=
    hasFDerivAt_boundaryStraighteningMap_id (n := n) (m := m) L hAL hFtildeAt
  have haInv : (fderiv ℝ G a).IsInvertible := by
    rw [hGderiv.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ Eₙ, rfl⟩
  obtain ⟨Ψ₀, haΨ, hΨV, _, hEq⟩ :=
    model_partialDiffeomorph_of_inverse_function_theorem
      (𝕜 := ℝ) (E := Eₙ) (F := Eₙ) (g := G) (a := a) (Ω := V) (T := (univ : Set Eₙ))
      (f' := ContinuousLinearEquiv.refl ℝ Eₙ)
      (hV.mem_nhds haV) hGOn (fun _ _ => trivial) hGAt hGderiv (by simp) haInv
  let Ψ : OpenPartialHomeomorph Eₙ Eₙ := Ψ₀.toOpenPartialHomeomorph
  have hcoe : ∀ z ∈ Ψ.source, Ψ z = G z := by
    intro z hz
    have hz' : z ∈ Ψ₀.source := hz
    exact (hEq hz').symm
  have hzero : ∀ z ∈ Ψ.source, Ψ z 0 = z 0 := by
    intro z hz
    rw [hcoe z hz]
    exact boundaryStraighteningMap_apply_zero (n := n) (m := m) L hNormal a ha0 Ftilde b z
  have hzeroSymm : ∀ z ∈ Ψ.target, Ψ.symm z 0 = z 0 := by
    intro w hw
    have hwSrc : Ψ.symm w ∈ Ψ.source := Ψ.map_target hw
    have hΨ : Ψ (Ψ.symm w) = w := Ψ.right_inv hw
    have : Ψ (Ψ.symm w) 0 = (Ψ.symm w) 0 := hzero _ hwSrc
    rw [hΨ] at this
    exact this.symm
  refine ⟨Ψ, haΨ, hΨV, hcoe, hzero, hzeroSymm, ?_, ?_⟩
  · exact (contMDiffOn_iff_contDiffOn (n := ∞)).1 Ψ₀.contMDiffOn_toFun
  · exact (contMDiffOn_iff_contDiffOn (n := ∞)).1 Ψ₀.contMDiffOn_invFun

theorem restrictToHalfSpace_mem_contDiffGroupoid
    {Ψ : OpenPartialHomeomorph Eₙ Eₙ}
    (hsrc : ∀ z ∈ Ψ.source, 0 ≤ z 0 → 0 ≤ Ψ z 0)
    (htgt : ∀ z ∈ Ψ.target, 0 ≤ z 0 → 0 ≤ Ψ.symm z 0)
    (hΨ : ContDiffOn ℝ ∞ (Ψ : Eₙ → Eₙ) Ψ.source)
    (hΨsymm : ContDiffOn ℝ ∞ Ψ.symm Ψ.target) :
    BoundaryPreimageCharts.restrictToHalfSpace (k := n + 1) Ψ hsrc htgt ∈
      contDiffGroupoid ∞ (𝓡∂ (n + 1)) := by
  let Φ := BoundaryPreimageCharts.restrictToHalfSpace (k := n + 1) Ψ hsrc htgt
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  refine ⟨?_, ?_⟩
  · change ContDiffOn ℝ ∞ ((𝓡∂ (n + 1)) ∘ Φ ∘ (𝓡∂ (n + 1)).symm)
      ((𝓡∂ (n + 1)).symm ⁻¹' Φ.source ∩ range (𝓡∂ (n + 1)))
    have hEq : EqOn ((𝓡∂ (n + 1)) ∘ Φ ∘ (𝓡∂ (n + 1)).symm) (Ψ : Eₙ → Eₙ)
        ((𝓡∂ (n + 1)).symm ⁻¹' Φ.source ∩ range (𝓡∂ (n + 1))) := by
      intro z hz
      have hzRange : z ∈ range (𝓡∂ (n + 1)) := hz.2
      have hz0 : 0 ≤ z 0 := by
        simpa [range_modelWithCornersEuclideanHalfSpace] using hzRange
      have hzSrc : ((𝓡∂ (n + 1)).symm z).1 ∈ Ψ.source := by
        have : (𝓡∂ (n + 1)).symm z ∈ Φ.source := hz.1
        simpa [Φ, BoundaryPreimageCharts.restrictToHalfSpace_source] using this
      have hzVal : ((𝓡∂ (n + 1)).symm z).1 = z :=
        CInfinityNeatSliceFamily.coe_modelWithCornersEuclideanHalfSpace_symm (n := n + 1) hzRange
      have hzSrc' : z ∈ Ψ.source := by simpa [hzVal] using hzSrc
      have happly :=
        BoundaryPreimageCharts.restrictToHalfSpace_apply (k := n + 1) Ψ hsrc htgt hzSrc
      change (Φ ((𝓡∂ (n + 1)).symm z)).1 = Ψ z
      rw [happly]
      change Ψ ((𝓡∂ (n + 1)).symm z).1 = Ψ z
      rw [hzVal]
    refine (hΨ.mono ?_).congr hEq
    intro z hz
    have hzRange : z ∈ range (𝓡∂ (n + 1)) := hz.2
    have hzVal : ((𝓡∂ (n + 1)).symm z).1 = z :=
      CInfinityNeatSliceFamily.coe_modelWithCornersEuclideanHalfSpace_symm (n := n + 1) hzRange
    have : ((𝓡∂ (n + 1)).symm z).1 ∈ Ψ.source := by
      have : (𝓡∂ (n + 1)).symm z ∈ Φ.source := hz.1
      simpa [Φ, BoundaryPreimageCharts.restrictToHalfSpace_source] using this
    simpa [hzVal] using this
  · change ContDiffOn ℝ ∞ ((𝓡∂ (n + 1)) ∘ Φ.symm ∘ (𝓡∂ (n + 1)).symm)
      ((𝓡∂ (n + 1)).symm ⁻¹' Φ.target ∩ range (𝓡∂ (n + 1)))
    have hEq : EqOn ((𝓡∂ (n + 1)) ∘ Φ.symm ∘ (𝓡∂ (n + 1)).symm) Ψ.symm
        ((𝓡∂ (n + 1)).symm ⁻¹' Φ.target ∩ range (𝓡∂ (n + 1))) := by
      intro z hz
      have hzRange : z ∈ range (𝓡∂ (n + 1)) := hz.2
      have hzVal : ((𝓡∂ (n + 1)).symm z).1 = z :=
        CInfinityNeatSliceFamily.coe_modelWithCornersEuclideanHalfSpace_symm (n := n + 1) hzRange
      have hzTgt : ((𝓡∂ (n + 1)).symm z).1 ∈ Ψ.target := by
        have : (𝓡∂ (n + 1)).symm z ∈ Φ.target := hz.1
        simpa [Φ, BoundaryPreimageCharts.restrictToHalfSpace] using this
      have hzTgt' : z ∈ Ψ.target := by simpa [hzVal] using hzTgt
      -- `restrictToHalfSpace` inverse is `⟨Ψ.symm z.1, _⟩` on the target.
      have happly :
          Φ.symm ((𝓡∂ (n + 1)).symm z) =
            ⟨Ψ.symm ((𝓡∂ (n + 1)).symm z).1, htgt _ hzTgt ((𝓡∂ (n + 1)).symm z).2⟩ := by
        simp [Φ, BoundaryPreimageCharts.restrictToHalfSpace, hzTgt]
      change (Φ.symm ((𝓡∂ (n + 1)).symm z)).1 = Ψ.symm z
      rw [happly]
      change Ψ.symm ((𝓡∂ (n + 1)).symm z).1 = Ψ.symm z
      rw [hzVal]
    refine (hΨsymm.mono ?_).congr hEq
    intro z hz
    have hzRange : z ∈ range (𝓡∂ (n + 1)) := hz.2
    have hzVal : ((𝓡∂ (n + 1)).symm z).1 = z :=
      CInfinityNeatSliceFamily.coe_modelWithCornersEuclideanHalfSpace_symm (n := n + 1) hzRange
    have : ((𝓡∂ (n + 1)).symm z).1 ∈ Ψ.target := by
      have : (𝓡∂ (n + 1)).symm z ∈ Φ.target := hz.1
      simpa [Φ, BoundaryPreimageCharts.restrictToHalfSpace] using this
    simpa [hzVal] using this

/-! ### Pointwise boundary neat-slice chart -/

/-- Pointwise boundary leaf: from derivative data at a single boundary fiber point, produce one
ambient neat-slice chart whose source contains that point.  The controller may assemble a
`CInfinityNeatSliceFamily` from these charts together with the interior leaf. -/
theorem exists_boundary_cInfinityNeatSliceChart
    {F : M → N} {c : N} {p : M} (hmn : m ≤ n)
    (hF : ContMDiff (𝓡∂ (n + 1)) (𝓡 m) ∞ F)
    (hpBoundary : p ∈ (𝓡∂ (n + 1)).boundary M) (hFp : F p = c)
    (hA : Function.Surjective
      (restrictToStandardBoundaryTangent (mfderiv (𝓡∂ (n + 1)) (𝓡 m) F p))) :
    ∃ D : CInfinityNeatSliceChart (d := n) (k := n - m) (q := m) (F ⁻¹' {c}),
      p ∈ D.ambientChart.source := by
  let a : Eₙ := extChartAt (𝓡∂ (n + 1)) p p
  have ha0 : a 0 = 0 := extChartAt_normal_eq_zero_of_mem_boundary hpBoundary
  have haRange : a ∈ range (𝓡∂ (n + 1)) := mem_range_self _
  let fRep : Eₙ → Eₘ := writtenInExtChartAt (𝓡∂ (n + 1)) (𝓡 m) p F
  let Ω₀ : Set Eₙ :=
    (extChartAt (𝓡∂ (n + 1)) p).target ∩
      (F ∘ (extChartAt (𝓡∂ (n + 1)) p).symm) ⁻¹' (extChartAt (𝓡 m) (F p)).source
  have hfRep : ContDiffOn ℝ ∞ fRep Ω₀ :=
    writtenInExtChartAt_contDiffOn_of_contMDiff (I := 𝓡∂ (n + 1)) (J := 𝓡 m) hF
  obtain ⟨W, hWopen, haW, hWslice⟩ :=
    exists_open_nhd_subset_writtenInExtChartAt_domain (F := F) (p := p) hF
  have hfRepW : ContDiffOn ℝ ∞ fRep (W ∩ range (𝓡∂ (n + 1))) :=
    hfRep.mono hWslice
  obtain ⟨V₀, hV₀open, haV₀, hV₀W, Ftilde, hFtildeOn, hEq⟩ :=
    contDiffOn_range_halfSpace_exists_open_extension_at
      (n := n + 1) (k := m) (W := W) (F := fRep)
      hWopen haW haRange ha0 hfRepW
  have hV₀slice : V₀ ∩ range (𝓡∂ (n + 1)) ⊆ Ω₀ :=
    (inter_subset_inter_left (range (𝓡∂ (n + 1))) hV₀W).trans hWslice
  have hFtildeAt : DifferentiableAt ℝ Ftilde a :=
    (hFtildeOn.differentiableOn (by simp)).differentiableAt (hV₀open.mem_nhds haV₀)
  have hAeq : fderiv ℝ Ftilde a = mfderiv (𝓡∂ (n + 1)) (𝓡 m) F p :=
    fderiv_eqOn_halfSpace_eq_mfderiv (F := F) (p := p) (V := V₀) (Ftilde := Ftilde)
      hF hV₀open haV₀ hEq hFtildeAt
  let A : Eₙ →L[ℝ] Eₘ := fderiv ℝ Ftilde a
  have hAsurj : Function.Surjective (restrictToStandardBoundaryTangent A) := by
    simpa [A, hAeq] using hA
  obtain ⟨L, hNormal, hAL⟩ := exists_normal_preserving_split (n := n) (m := m) hmn A hAsurj
  let b : Eₘ := Ftilde a
  have hHas : HasFDerivAt Ftilde A a := hFtildeAt.hasFDerivAt
  obtain ⟨Ψ, haΨ, hΨV, hΨG, hΨ0, hΨsymm0, hΨdiff, hΨsymmDiff⟩ :=
    exists_normal_preserving_ift_branch (n := n) (m := m) L hNormal hAL ha0
      hV₀open haV₀ hFtildeOn hHas
  have hsrc : ∀ z ∈ Ψ.source, 0 ≤ z 0 → 0 ≤ Ψ z 0 := by
    intro z hz hz0
    rw [hΨ0 z hz]
    exact hz0
  have htgt : ∀ z ∈ Ψ.target, 0 ≤ z 0 → 0 ≤ Ψ.symm z 0 := by
    intro z hz hz0
    rw [hΨsymm0 z hz]
    exact hz0
  let Φ := BoundaryPreimageCharts.restrictToHalfSpace (k := n + 1) Ψ hsrc htgt
  have hΦgroup : Φ ∈ contDiffGroupoid ∞ (𝓡∂ (n + 1)) :=
    restrictToHalfSpace_mem_contDiffGroupoid (n := n) hsrc htgt hΨdiff hΨsymmDiff
  let e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
    chartAt (EuclideanHalfSpace (n + 1)) p
  let ambient : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) := e.trans Φ
  have heMax : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) ∞ M :=
    chart_mem_maximalAtlas (I := 𝓡∂ (n + 1)) p
  have hΦcont : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ Φ Φ.source :=
    contMDiffOn_of_mem_contDiffGroupoid hΦgroup
  have hΦsymmCont : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ Φ.symm Φ.target :=
    contMDiffOn_of_mem_contDiffGroupoid ((contDiffGroupoid ∞ (𝓡∂ (n + 1))).symm hΦgroup)
  have heCont : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ e e.source :=
    contMDiffOn_of_mem_maximalAtlas heMax
  have heSymmCont : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas heMax
  have hAmbCont : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ ambient ambient.source := by
    change ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ (Φ ∘ e)
      (e.source ∩ e ⁻¹' Φ.source)
    exact hΦcont.comp (heCont.mono inter_subset_left) (fun _ hx => hx.2)
  have hAmbSymmCont : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ ambient.symm
      ambient.target := by
    change ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ (e.symm ∘ Φ.symm)
      (Φ.target ∩ Φ.symm ⁻¹' e.target)
    exact heSymmCont.comp (hΦsymmCont.mono inter_subset_left) (fun _ hx => hx.2)
  have hAmbMax : ambient ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) ∞ M :=
    ambient.mem_maximalAtlas_of_contMDiffOn hAmbCont hAmbSymmCont
  have hpAmb : p ∈ ambient.source := by
    change p ∈ e.source ∩ e ⁻¹' Φ.source
    refine ⟨mem_chart_source _ p, ?_⟩
    have : (e p).1 = a := rfl
    have haHalf : (e p).1 ∈ Ψ.source := by simpa [this] using haΨ
    simpa [Φ, BoundaryPreimageCharts.restrictToHalfSpace_source] using haHalf
  have himage : ambient '' ((F ⁻¹' {c}) ∩ ambient.source) =
      neatHalfSpaceSlice (d := n) (k := n - m) (q := m) ambient.target L := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyS, hySrc⟩, rfl⟩
      refine ⟨ambient.map_source hySrc, ?_⟩
      change (L.symm (ambient y).1).2 = 0
      have hyE : y ∈ e.source := hySrc.1
      have hyΦ : e y ∈ Φ.source := hySrc.2
      have hyΨ : (e y).1 ∈ Ψ.source := by
        simpa [Φ, BoundaryPreimageCharts.restrictToHalfSpace_source] using hyΦ
      have hΦy :=
        BoundaryPreimageCharts.restrictToHalfSpace_apply (k := n + 1) Ψ hsrc htgt hyΨ
      have hAmbY : (ambient y).1 = Ψ (e y).1 := by
        change (Φ (e y)).1 = Ψ (e y).1
        rw [hΦy]
      have hGy : Ψ (e y).1 =
          boundaryStraighteningMap (n := n) (m := m) L a Ftilde b (e y).1 :=
        hΨG _ hyΨ
      have hwV : (e y).1 ∈ V₀ := hΨV hyΨ
      have hwRange : (e y).1 ∈ range (𝓡∂ (n + 1)) := ⟨e y, rfl⟩
      have hFtildeEq : Ftilde (e y).1 = fRep (e y).1 :=
        hEq ⟨hwV, hwRange⟩
      have hyExt : (e y).1 ∈ Ω₀ := hV₀slice ⟨hwV, hwRange⟩
      have hyExtSrc : y ∈ (extChartAt (𝓡∂ (n + 1)) p).source := by
        simpa [extChartAt_source] using hyE
      have hyLeft : (extChartAt (𝓡∂ (n + 1)) p).symm (e y).1 = y := by
        change (extChartAt (𝓡∂ (n + 1)) p).symm (extChartAt (𝓡∂ (n + 1)) p y) = y
        exact (extChartAt (𝓡∂ (n + 1)) p).left_inv hyExtSrc
      have hRep : fRep (e y).1 = extChartAt (𝓡 m) (F p) (F y) := by
        change extChartAt (𝓡 m) (F p)
            (F ((extChartAt (𝓡∂ (n + 1)) p).symm (e y).1)) =
          extChartAt (𝓡 m) (F p) (F y)
        rw [hyLeft]
      have hFySrc : F y ∈ (extChartAt (𝓡 m) (F p)).source := by
        have : F ((extChartAt (𝓡∂ (n + 1)) p).symm (e y).1) ∈
            (extChartAt (𝓡 m) (F p)).source := hyExt.2
        rwa [hyLeft] at this
      have hFc : extChartAt (𝓡 m) (F p) (F y) = extChartAt (𝓡 m) (F p) (F p) := by
        have hyF : F y = F p := (show F y = c from hyS).trans hFp.symm
        rw [hyF]
      have haRep : Ftilde a = fRep a := hEq ⟨haV₀, haRange⟩
      have haRep' : fRep a = extChartAt (𝓡 m) (F p) (F p) := by
        change extChartAt (𝓡 m) (F p)
            (F ((extChartAt (𝓡∂ (n + 1)) p).symm (extChartAt (𝓡∂ (n + 1)) p p))) =
          extChartAt (𝓡 m) (F p) (F p)
        rw [(extChartAt (𝓡∂ (n + 1)) p).left_inv (mem_extChartAt_source p)]
      have hb : b = extChartAt (𝓡 m) (F p) (F p) := haRep.trans haRep'
      have hG2 :
          (L.symm (boundaryStraighteningMap (n := n) (m := m) L a Ftilde b (e y).1)).2 =
            Ftilde (e y).1 - b := by
        change (L.symm (L ((L.symm ((e y).1 - a)).1, Ftilde (e y).1 - b))).2 =
          Ftilde (e y).1 - b
        simp
      rw [hAmbY, hGy, hG2, hFtildeEq, hRep, hFc, hb, sub_self]
    · intro hz
      have hzT : z ∈ ambient.target := hz.1
      have hzTail : (L.symm z.1).2 = 0 := hz.2
      let y : M := ambient.symm z
      have hySrc : y ∈ ambient.source := ambient.map_target hzT
      have hyE : y ∈ e.source := hySrc.1
      have hyΦ : e y ∈ Φ.source := hySrc.2
      have hyΨ : (e y).1 ∈ Ψ.source := by
        simpa [Φ, BoundaryPreimageCharts.restrictToHalfSpace_source] using hyΦ
      have hΦy :=
        BoundaryPreimageCharts.restrictToHalfSpace_apply (k := n + 1) Ψ hsrc htgt hyΨ
      have hAmbY : (ambient y).1 = Ψ (e y).1 := by
        change (Φ (e y)).1 = Ψ (e y).1
        rw [hΦy]
      have hyRight : ambient y = z := ambient.right_inv hzT
      have hGy : Ψ (e y).1 =
          boundaryStraighteningMap (n := n) (m := m) L a Ftilde b (e y).1 :=
        hΨG _ hyΨ
      have hG2 :
          (L.symm (boundaryStraighteningMap (n := n) (m := m) L a Ftilde b (e y).1)).2 =
            Ftilde (e y).1 - b := by
        change (L.symm (L ((L.symm ((e y).1 - a)).1, Ftilde (e y).1 - b))).2 =
          Ftilde (e y).1 - b
        simp
      have hTail : Ftilde (e y).1 - b = 0 := by
        have : (L.symm z.1).2 = Ftilde (e y).1 - b := by
          rw [← hyRight, hAmbY, hGy, hG2]
        exact this.symm.trans hzTail
      have hwV : (e y).1 ∈ V₀ := hΨV hyΨ
      have hwRange : (e y).1 ∈ range (𝓡∂ (n + 1)) := ⟨e y, rfl⟩
      have hyExt : (e y).1 ∈ Ω₀ := hV₀slice ⟨hwV, hwRange⟩
      have hFtildeEq : Ftilde (e y).1 = fRep (e y).1 :=
        hEq ⟨hwV, hwRange⟩
      have hyExtSrc : y ∈ (extChartAt (𝓡∂ (n + 1)) p).source := by
        simpa [extChartAt_source] using hyE
      have hyLeft : (extChartAt (𝓡∂ (n + 1)) p).symm (e y).1 = y := by
        change (extChartAt (𝓡∂ (n + 1)) p).symm (extChartAt (𝓡∂ (n + 1)) p y) = y
        exact (extChartAt (𝓡∂ (n + 1)) p).left_inv hyExtSrc
      have hRep : fRep (e y).1 = extChartAt (𝓡 m) (F p) (F y) := by
        change extChartAt (𝓡 m) (F p)
            (F ((extChartAt (𝓡∂ (n + 1)) p).symm (e y).1)) =
          extChartAt (𝓡 m) (F p) (F y)
        rw [hyLeft]
      have hFySrc : F y ∈ (extChartAt (𝓡 m) (F p)).source := by
        have : F ((extChartAt (𝓡∂ (n + 1)) p).symm (e y).1) ∈
            (extChartAt (𝓡 m) (F p)).source := hyExt.2
        rwa [hyLeft] at this
      have haRep : Ftilde a = fRep a := hEq ⟨haV₀, haRange⟩
      have haRep' : fRep a = extChartAt (𝓡 m) (F p) (F p) := by
        change extChartAt (𝓡 m) (F p)
            (F ((extChartAt (𝓡∂ (n + 1)) p).symm (extChartAt (𝓡∂ (n + 1)) p p))) =
          extChartAt (𝓡 m) (F p) (F p)
        rw [(extChartAt (𝓡∂ (n + 1)) p).left_inv (mem_extChartAt_source p)]
      have hb : b = extChartAt (𝓡 m) (F p) (F p) := haRep.trans haRep'
      have hChartEq' : extChartAt (𝓡 m) (F p) (F y) = extChartAt (𝓡 m) (F p) (F p) := by
        calc
          extChartAt (𝓡 m) (F p) (F y) = fRep (e y).1 := hRep.symm
          _ = Ftilde (e y).1 := hFtildeEq.symm
          _ = b := sub_eq_zero.mp hTail
          _ = extChartAt (𝓡 m) (F p) (F p) := hb
      have hyFp : F y ∈ (extChartAt (𝓡 m) (F p)).source := hFySrc
      have hpSrc : F p ∈ (extChartAt (𝓡 m) (F p)).source :=
        mem_extChartAt_source (I := 𝓡 m) (F p)
      have hyF : F y = F p :=
        (extChartAt (𝓡 m) (F p)).injOn hyFp hpSrc hChartEq'
      have hyS : y ∈ F ⁻¹' {c} := by
        change F y = c
        rw [hyF, hFp]
      exact ⟨y, ⟨hyS, hySrc⟩, hyRight⟩
  refine
    ⟨{ ambientChart := ambient
       ambient_mem_maximalAtlas := hAmbMax
       equiv := L
       normal_eq := hNormal
       image_eq := himage }, hpAmb⟩

/-- Variant that reads the pointwise derivative hypothesis from the global boundary-regularity
predicate. -/
theorem exists_boundary_cInfinityNeatSliceChart_of_isBoundaryRegularValue
    {F : M → N} {c : N} {p : M} (hmn : m ≤ n)
    (hF : ContMDiff (𝓡∂ (n + 1)) (𝓡 m) ∞ F)
    (hBoundary : IsBoundaryRegularValue n m F c)
    (hpBoundary : p ∈ (𝓡∂ (n + 1)).boundary M) (hFp : F p = c) :
    ∃ D : CInfinityNeatSliceChart (d := n) (k := n - m) (q := m) (F ⁻¹' {c}),
      p ∈ D.ambientChart.source :=
  exists_boundary_cInfinityNeatSliceChart (hmn := hmn) (hF := hF)
    (hpBoundary := hpBoundary) (hFp := hFp)
    (hA := hBoundary p hpBoundary hFp)

end Manifold.BoundaryRegularPreimageChart
