import LeeSmoothLib.Ch05.Sec05_37.CInfinityHalfSpaceAtlas

/-!
# Neat half-space slices and their induced `C∞` atlas

The free coordinates of a neat slice include the distinguished normal coordinate.  Thus a linear
equivalence `L : ℝᵏ × ℝᑫ ≃L ℝᵈ` with
`(L (u,v)) 0 = u 0` sends `ℍᵏ × ℝᑫ` to `ℍᵈ`, and the zero-complement slice is itself modeled on
`ℍᵏ`.  This is the coordinate geometry needed by Problem 5-23.
-/

open Set ChartedSpace
open scoped ContDiff Manifold

noncomputable section

namespace Manifold

universe u

section Geometry

variable {d k q : ℕ}

/-- Insert the free half-space coordinates with zero complementary coordinates. -/
def neatHalfSpaceInclusion
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    (u : EuclideanHalfSpace (k + 1)) : EuclideanHalfSpace (d + 1) :=
  ⟨L (u.1, 0), by rw [hNormal]; exact u.2⟩

/-- Project an ambient half-space point to the free coordinates of a normal-preserving split. -/
def neatHalfSpaceProjection
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    (z : EuclideanHalfSpace (d + 1)) : EuclideanHalfSpace (k + 1) :=
  ⟨(L.symm z.1).1, by
    have hz := hNormal (L.symm z.1).1 (L.symm z.1).2
    rw [L.apply_symm_apply] at hz
    rw [← hz]
    exact z.2⟩

@[simp] theorem neatHalfSpaceProjection_inclusion
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    (u : EuclideanHalfSpace (k + 1)) :
    neatHalfSpaceProjection L hNormal (neatHalfSpaceInclusion L hNormal u) = u := by
  apply Subtype.ext
  simp [neatHalfSpaceProjection, neatHalfSpaceInclusion]

theorem neatHalfSpaceInclusion_projection_of_tail_eq_zero
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    {z : EuclideanHalfSpace (d + 1)} (hz : (L.symm z.1).2 = 0) :
    neatHalfSpaceInclusion L hNormal (neatHalfSpaceProjection L hNormal z) = z := by
  apply Subtype.ext
  change L ((L.symm z.1).1, 0) = z.1
  rw [← hz, Prod.eta, L.apply_symm_apply]

theorem continuous_neatHalfSpaceInclusion
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0) :
    Continuous (neatHalfSpaceInclusion L hNormal) := by
  apply Continuous.subtype_mk
  exact L.continuous.comp (continuous_subtype_val.prodMk continuous_const)

theorem continuous_neatHalfSpaceProjection
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0) :
    Continuous (neatHalfSpaceProjection L hNormal) := by
  apply Continuous.subtype_mk
  exact continuous_fst.comp (L.symm.continuous.comp continuous_subtype_val)

/-- The part of `U` on which the complementary coordinates of `L` vanish. -/
def neatHalfSpaceSlice
    (U : Set (EuclideanHalfSpace (d + 1)))
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1))) : Set (EuclideanHalfSpace (d + 1)) :=
  {z | z ∈ U ∧ (L.symm z.1).2 = 0}

/-- Projection identifies a neat half-space slice with the open part of `ℍᵏ` whose zero-tail
inclusion lies in `U`. -/
def neatHalfSpaceSliceHomeomorph
    (U : Set (EuclideanHalfSpace (d + 1)))
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0) :
    neatHalfSpaceSlice U L ≃ₜ
      {u : EuclideanHalfSpace (k + 1) | neatHalfSpaceInclusion L hNormal u ∈ U} where
  toFun z := ⟨neatHalfSpaceProjection L hNormal z.1, by
    change neatHalfSpaceInclusion L hNormal (neatHalfSpaceProjection L hNormal z.1) ∈ U
    rw [neatHalfSpaceInclusion_projection_of_tail_eq_zero L hNormal z.2.2]
    exact z.2.1⟩
  invFun u := ⟨neatHalfSpaceInclusion L hNormal u.1, by
    constructor
    · exact u.2
    · change (L.symm (L (u.1.1, 0))).2 = 0
      simp⟩
  left_inv z := by
    apply Subtype.ext
    exact neatHalfSpaceInclusion_projection_of_tail_eq_zero L hNormal z.2.2
  right_inv u := by
    apply Subtype.ext
    exact neatHalfSpaceProjection_inclusion L hNormal u.1
  continuous_toFun := Continuous.subtype_mk
    ((continuous_neatHalfSpaceProjection L hNormal).comp continuous_subtype_val)
    (fun z ↦ by
      change neatHalfSpaceInclusion L hNormal (neatHalfSpaceProjection L hNormal z.1) ∈ U
      rw [neatHalfSpaceInclusion_projection_of_tail_eq_zero L hNormal z.2.2]
      exact z.2.1)
  continuous_invFun := Continuous.subtype_mk
    ((continuous_neatHalfSpaceInclusion L hNormal).comp continuous_subtype_val)
    (fun u ↦ by
      constructor
      · exact u.2
      · change (L.symm (L (u.1.1, 0))).2 = 0
        simp)

/-- The open target of the neat-slice chart. -/
def neatHalfSpaceTargetOpen
    (U : Set (EuclideanHalfSpace (d + 1))) (hU : IsOpen U)
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0) :
    TopologicalSpace.Opens (EuclideanHalfSpace (k + 1)) :=
  ⟨{u | neatHalfSpaceInclusion L hNormal u ∈ U},
    hU.preimage (continuous_neatHalfSpaceInclusion L hNormal)⟩

/-- A neat slice, pointed at `z`, has a canonical chart in the standard half-space `ℍᵏ`. -/
def neatHalfSpaceSlicePartialHomeomorph
    (U : Set (EuclideanHalfSpace (d + 1))) (hU : IsOpen U)
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    (z : neatHalfSpaceSlice U L) :
    OpenPartialHomeomorph (neatHalfSpaceSlice U L) (EuclideanHalfSpace (k + 1)) :=
  let V := neatHalfSpaceTargetOpen U hU L hNormal
  let hzV : Nonempty V :=
    ⟨⟨neatHalfSpaceProjection L hNormal z.1, by
      change neatHalfSpaceInclusion L hNormal (neatHalfSpaceProjection L hNormal z.1) ∈ U
      rw [neatHalfSpaceInclusion_projection_of_tail_eq_zero L hNormal z.2.2]
      exact z.2.1⟩⟩
  (neatHalfSpaceSliceHomeomorph U L hNormal).toOpenPartialHomeomorph.trans
    (V.openPartialHomeomorphSubtypeCoe hzV)

theorem neatHalfSpaceSlicePartialHomeomorph_mem_source
    (U : Set (EuclideanHalfSpace (d + 1))) (hU : IsOpen U)
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    (z : neatHalfSpaceSlice U L) :
    z ∈ (neatHalfSpaceSlicePartialHomeomorph U hU L hNormal z).source := by
  simp [neatHalfSpaceSlicePartialHomeomorph]

end Geometry

section InducedChart

variable {d k q : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (d + 1)) M]
  [IsManifold (𝓡∂ (d + 1)) ∞ M]
variable (S : Set M)

/-- A smooth ambient chart in which `S` is a normal-preserving zero-complement slice. -/
structure CInfinityNeatSliceChart where
  ambientChart : OpenPartialHomeomorph M (EuclideanHalfSpace (d + 1))
  ambient_mem_maximalAtlas : ambientChart ∈
    IsManifold.maximalAtlas (𝓡∂ (d + 1)) ∞ M
  equiv : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
    EuclideanSpace ℝ (Fin (d + 1))
  normal_eq : ∀ u v, (equiv (u, v)) 0 = u 0
  image_eq : ambientChart '' (S ∩ ambientChart.source) =
    neatHalfSpaceSlice ambientChart.target equiv

namespace CInfinityNeatSliceChart

variable {S : Set M}

/-- The open part of the subtype cut out by the ambient chart source. -/
def subtypeSourcePatch (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S) :
    TopologicalSpace.Opens S :=
  ⟨{y : S | y.1 ∈ D.ambientChart.source}, by
    simpa [Set.preimage, Function.comp] using
      D.ambientChart.open_source.preimage continuous_subtype_val⟩

/-- Forgetting the nested subtype identifies the source patch with `S ∩ source`. -/
def subtypePatchIntersectionHomeomorph
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S) :
    {y : S | y.1 ∈ D.ambientChart.source} ≃ₜ
      (S ∩ D.ambientChart.source : Set M) where
  toEquiv := Equiv.subtypeSubtypeEquivSubtypeInter (fun x : M ↦ x ∈ S)
    (fun x : M ↦ x ∈ D.ambientChart.source)
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := by
    have hToS : Continuous fun y : (S ∩ D.ambientChart.source : Set M) ↦
        (⟨y.1, y.2.1⟩ : S) :=
      Continuous.subtype_mk continuous_subtype_val _
    exact Continuous.subtype_mk hToS _

/-- The subtype source patch is homeomorphic to the neat slice in ambient coordinates. -/
def patchToNeatSliceHomeomorph
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S) :
    {y : S | y.1 ∈ D.ambientChart.source} ≃ₜ
      neatHalfSpaceSlice D.ambientChart.target D.equiv :=
  D.subtypePatchIntersectionHomeomorph.trans
    (D.ambientChart.homeomorphOfImageSubsetSource (fun _ hy ↦ hy.2) D.image_eq)

/-- The chart on a source patch obtained by projecting the ambient neat-slice coordinates. -/
def patchChart
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S)
    (x : S) (hx : x.1 ∈ D.ambientChart.source) :
    OpenPartialHomeomorph D.subtypeSourcePatch (EuclideanHalfSpace (k + 1)) := by
  let xPatch : {y : S | y.1 ∈ D.ambientChart.source} := ⟨x, hx⟩
  let xSlice : neatHalfSpaceSlice D.ambientChart.target D.equiv :=
    D.patchToNeatSliceHomeomorph xPatch
  change OpenPartialHomeomorph {y : S | y.1 ∈ D.ambientChart.source}
    (EuclideanHalfSpace (k + 1))
  exact D.patchToNeatSliceHomeomorph.toOpenPartialHomeomorph.trans
    (neatHalfSpaceSlicePartialHomeomorph D.ambientChart.target
      D.ambientChart.open_target D.equiv D.normal_eq xSlice)

/-- Extend the patch chart back to a pointed chart on all of the subtype. -/
def pointedSubtypeChart
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S)
    (x : S) (hx : x.1 ∈ D.ambientChart.source) :
    OpenPartialHomeomorph S (EuclideanHalfSpace (k + 1)) :=
  let P := D.subtypeSourcePatch
  let xP : P := ⟨x, hx⟩
  ((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans (D.patchChart x hx)

theorem patchChart_mem_source
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S)
    (x : S) (hx : x.1 ∈ D.ambientChart.source) :
    (⟨x, hx⟩ : D.subtypeSourcePatch) ∈ (D.patchChart x hx).source := by
  let xPatch : {y : S | y.1 ∈ D.ambientChart.source} := ⟨x, hx⟩
  let xSlice : neatHalfSpaceSlice D.ambientChart.target D.equiv :=
    D.patchToNeatSliceHomeomorph xPatch
  change xPatch ∈
    (D.patchToNeatSliceHomeomorph.toOpenPartialHomeomorph.trans
      (neatHalfSpaceSlicePartialHomeomorph D.ambientChart.target
        D.ambientChart.open_target D.equiv D.normal_eq xSlice)).source
  rw [OpenPartialHomeomorph.trans_source]
  exact ⟨Set.mem_univ _, by
    simpa [xSlice] using
      neatHalfSpaceSlicePartialHomeomorph_mem_source D.ambientChart.target
        D.ambientChart.open_target D.equiv D.normal_eq xSlice⟩

theorem pointedSubtypeChart_mem_source
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S)
    (x : S) (hx : x.1 ∈ D.ambientChart.source) :
    x ∈ (D.pointedSubtypeChart x hx).source := by
  let P := D.subtypeSourcePatch
  let xP : P := ⟨x, hx⟩
  change x ∈ (((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans
    (D.patchChart x hx)).source
  rw [OpenPartialHomeomorph.trans_source]
  have hxTarget : x ∈ (P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).target := by
    rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    exact hx
  refine ⟨hxTarget, ?_⟩
  have hxPatch :
      ((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm x : P) = ⟨x, hx⟩ := by
    apply Subtype.ext
    simpa [P, xP, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
      (P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).right_inv hxTarget
  change ((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm x : P) ∈
    (D.patchChart x hx).source
  rw [hxPatch]
  exact D.patchChart_mem_source x hx

theorem pointedSubtypeChart_source_subset_ambient_source
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S)
    (x : S) (hx : x.1 ∈ D.ambientChart.source) {y : S}
    (hy : y ∈ (D.pointedSubtypeChart x hx).source) :
    y.1 ∈ D.ambientChart.source := by
  let P := D.subtypeSourcePatch
  let xP : P := ⟨x, hx⟩
  change y ∈ (((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans
    (D.patchChart x hx)).source at hy
  rw [OpenPartialHomeomorph.trans_source] at hy
  have hyP : y ∈ (P : Set S) := by
    simpa using hy.1
  exact hyP

@[simp] theorem neatHalfSpaceSlicePartialHomeomorph_apply
    (U : Set (EuclideanHalfSpace (d + 1))) (hU : IsOpen U)
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    (z₀ z : neatHalfSpaceSlice U L) :
    neatHalfSpaceSlicePartialHomeomorph U hU L hNormal z₀ z =
      neatHalfSpaceProjection L hNormal z.1 := by
  rfl

@[simp] theorem patchToNeatSliceHomeomorph_apply
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S)
    (y : {y : S | y.1 ∈ D.ambientChart.source}) :
    (D.patchToNeatSliceHomeomorph y).1 = D.ambientChart y.1.1 := by
  rfl

theorem patchChart_apply
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S)
    (x : S) (hx : x.1 ∈ D.ambientChart.source)
    (y : D.subtypeSourcePatch) :
    D.patchChart x hx y =
      neatHalfSpaceProjection D.equiv D.normal_eq (D.ambientChart y.1.1) := by
  rfl

theorem pointedSubtypeChart_apply
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S)
    (x : S) (hx : x.1 ∈ D.ambientChart.source) {y : S}
    (hy : y ∈ (D.pointedSubtypeChart x hx).source) :
    D.pointedSubtypeChart x hx y =
      neatHalfSpaceProjection D.equiv D.normal_eq (D.ambientChart y.1) := by
  let P := D.subtypeSourcePatch
  let xP : P := ⟨x, hx⟩
  change y ∈ (((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans
    (D.patchChart x hx)).source at hy
  rw [OpenPartialHomeomorph.trans_source] at hy
  change (((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans
    (D.patchChart x hx)) y = _
  rw [OpenPartialHomeomorph.trans_apply]
  have hyTarget : y ∈ (P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).target := hy.1
  have hsymm :
      ((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm y : P) =
        ⟨y, by
          rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] at hyTarget
          exact hyTarget⟩ := by
    apply Subtype.ext
    simpa using (P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).right_inv hyTarget
  rw [hsymm]
  exact D.patchChart_apply x hx _

theorem ambientChart_symm_pointedSubtypeChart
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S)
    (x : S) (hx : x.1 ∈ D.ambientChart.source)
    {z : EuclideanHalfSpace (k + 1)}
    (hz : z ∈ (D.pointedSubtypeChart x hx).target) :
    D.ambientChart ((D.pointedSubtypeChart x hx).symm z).1 =
      neatHalfSpaceInclusion D.equiv D.normal_eq z := by
  let eS := D.pointedSubtypeChart x hx
  let y : S := eS.symm z
  have hySource : y ∈ eS.source := eS.symm.map_source hz
  have hyAmbient : y.1 ∈ D.ambientChart.source :=
    D.pointedSubtypeChart_source_subset_ambient_source x hx hySource
  have hyImage : D.ambientChart y.1 ∈
      neatHalfSpaceSlice D.ambientChart.target D.equiv := by
    rw [← D.image_eq]
    exact ⟨y.1, ⟨y.2, hyAmbient⟩, rfl⟩
  have hproj :
      neatHalfSpaceProjection D.equiv D.normal_eq (D.ambientChart y.1) = z := by
    rw [← D.pointedSubtypeChart_apply x hx hySource]
    exact eS.right_inv hz
  calc
    D.ambientChart y.1 =
        neatHalfSpaceInclusion D.equiv D.normal_eq
          (neatHalfSpaceProjection D.equiv D.normal_eq (D.ambientChart y.1)) :=
      (neatHalfSpaceInclusion_projection_of_tail_eq_zero
        D.equiv D.normal_eq hyImage.2).symm
    _ = neatHalfSpaceInclusion D.equiv D.normal_eq z := by rw [hproj]

theorem pointedSubtypeChart_normal_eq_ambient
    (D : CInfinityNeatSliceChart (d := d) (k := k) (q := q) S)
    (x : S) (hx : x.1 ∈ D.ambientChart.source) :
    (D.pointedSubtypeChart x hx x).1 0 = (D.ambientChart x.1).1 0 := by
  rw [D.pointedSubtypeChart_apply x hx (D.pointedSubtypeChart_mem_source x hx)]
  change (D.equiv.symm (D.ambientChart x.1).1).1 0 = (D.ambientChart x.1).1 0
  have h := D.normal_eq
    (D.equiv.symm (D.ambientChart x.1).1).1
    (D.equiv.symm (D.ambientChart x.1).1).2
  rw [D.equiv.apply_symm_apply] at h
  exact h.symm

end CInfinityNeatSliceChart

end InducedChart

section Family

variable {d k q : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (d + 1)) M]
  [IsManifold (𝓡∂ (d + 1)) ∞ M]
variable (S : Set M)

/-- A covering family of ambient neat-slice charts.  Problem 5-23 constructs one directly from
the ordinary inverse function theorem; no fiber atlas is included in this input. -/
structure CInfinityNeatSliceFamily where
  localChart : S → CInfinityNeatSliceChart (d := d) (k := k) (q := q) S
  mem_ambient_source : ∀ x, x.1 ∈ (localChart x).ambientChart.source

namespace CInfinityNeatSliceFamily

variable {S : Set M}

/-- The pointed fiber chart induced by the chosen ambient neat-slice chart. -/
def fiberChart (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x : S) :
    OpenPartialHomeomorph S (EuclideanHalfSpace (k + 1)) :=
  (D.localChart x).pointedSubtypeChart x (D.mem_ambient_source x)

theorem mem_fiberChart_source
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x : S) :
    x ∈ (D.fiberChart x).source :=
  (D.localChart x).pointedSubtypeChart_mem_source x (D.mem_ambient_source x)

theorem fiberChart_source_subset_ambient_source
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S)
    (x : S) {y : S} (hy : y ∈ (D.fiberChart x).source) :
    y.1 ∈ (D.localChart x).ambientChart.source :=
  (D.localChart x).pointedSubtypeChart_source_subset_ambient_source
    x (D.mem_ambient_source x) hy

theorem ambientChart_symm_fiberChart
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S)
    (x : S) {z : EuclideanHalfSpace (k + 1)}
    (hz : z ∈ (D.fiberChart x).target) :
    (D.localChart x).ambientChart ((D.fiberChart x).symm z).1 =
      neatHalfSpaceInclusion (D.localChart x).equiv (D.localChart x).normal_eq z :=
  (D.localChart x).ambientChart_symm_pointedSubtypeChart
    x (D.mem_ambient_source x) hz

/-- The ambient-coordinate transition between two neat-slice charts is `C∞` on its natural
extended source. -/
theorem ambientTransition_contDiffOn
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x y : S) :
    let ex := (D.localChart x).ambientChart
    let ey := (D.localChart y).ambientChart
    ContDiffOn ℝ ∞
      ((𝓡∂ (d + 1)) ∘ (ex.symm.trans ey) ∘ (𝓡∂ (d + 1)).symm)
      ((𝓡∂ (d + 1)).symm ⁻¹' (ex.symm.trans ey).source ∩
        range (𝓡∂ (d + 1))) := by
  dsimp only
  have hcompat :
      ((D.localChart x).ambientChart.symm.trans
          (D.localChart y).ambientChart) ∈
        contDiffGroupoid ∞ (𝓡∂ (d + 1)) :=
    IsManifold.compatible_of_mem_maximalAtlas
      (D.localChart x).ambient_mem_maximalAtlas
      (D.localChart y).ambient_mem_maximalAtlas
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at hcompat
  exact hcompat.1

/-- Euclidean spelling of a normal-preserving inclusion. -/
def inclusionEuclidean
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (d + 1)) :=
  fun u ↦ L (u, 0)

/-- Euclidean spelling of a normal-preserving projection. -/
def projectionEuclidean
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (k + 1)) :=
  fun z ↦ (L.symm z).1

theorem contDiff_inclusionEuclidean
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1))) :
    ContDiff ℝ ∞ (inclusionEuclidean (k := k) (q := q) (d := d) L) :=
  L.contDiff.comp (contDiff_id.prodMk contDiff_const)

theorem contDiff_projectionEuclidean
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1))) :
    ContDiff ℝ ∞ (projectionEuclidean (k := k) (q := q) (d := d) L) :=
  contDiff_fst.comp L.symm.contDiff

theorem coe_modelWithCornersEuclideanHalfSpace_symm
    {n : ℕ} [NeZero n] {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ range (𝓡∂ n)) : ((𝓡∂ n).symm z).1 = z := by
  change (𝓡∂ n) ((𝓡∂ n).symm z) = z
  exact (𝓡∂ n).right_inv hz

theorem inclusionEuclidean_nonneg
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    {z : EuclideanSpace ℝ (Fin (k + 1))} (hz0 : 0 ≤ z 0) :
    0 ≤ inclusionEuclidean L z 0 := by
  simpa [inclusionEuclidean, hNormal] using hz0

theorem inclusionEuclidean_mem_range
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    {z : EuclideanSpace ℝ (Fin (k + 1))} (hz0 : 0 ≤ z 0) :
    inclusionEuclidean L z ∈ range (𝓡∂ (d + 1)) := by
  refine ⟨⟨inclusionEuclidean L z, inclusionEuclidean_nonneg L hNormal hz0⟩, rfl⟩

theorem writtenInExtend_of_fiberChart
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x : S) :
    EqOn
      (((D.localChart x).ambientChart.extend (𝓡∂ (d + 1))) ∘ Subtype.val ∘
        ((D.fiberChart x).extend (𝓡∂ (k + 1))).symm)
      (((D.localChart x).equiv) ∘ (·, 0))
      ((D.fiberChart x).extend (𝓡∂ (k + 1))).target := by
  intro z hz
  have hz' : z ∈ (𝓡∂ (k + 1)).symm ⁻¹' (D.fiberChart x).target ∩
      range (𝓡∂ (k + 1)) := by
    rwa [← (D.fiberChart x).extend_target]
  have hinc := D.ambientChart_symm_fiberChart x hz'.1
  have hzVal := coe_modelWithCornersEuclideanHalfSpace_symm hz'.2
  change ((D.localChart x).ambientChart
      ((D.fiberChart x).symm ((𝓡∂ (k + 1)).symm z)).1).1 =
    (D.localChart x).equiv (z, 0)
  rw [hinc]
  change (D.localChart x).equiv (((𝓡∂ (k + 1)).symm z).1, 0) =
    (D.localChart x).equiv (z, 0)
  rw [hzVal]

theorem fiberChart_normal_eq_ambient
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x : S) :
    ((D.fiberChart x) x).1 0 =
      ((D.localChart x).ambientChart x.1).1 0 :=
  (D.localChart x).pointedSubtypeChart_normal_eq_ambient x (D.mem_ambient_source x)

theorem fiberChart_source_subset
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x : S) :
    (D.fiberChart x).source ⊆ Subtype.val ⁻¹' (D.localChart x).ambientChart.source := by
  intro y hy
  exact D.fiberChart_source_subset_ambient_source x hy

theorem ambient_of_fiberChart_symm_eq_inclusion
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x : S)
    {w : EuclideanHalfSpace (k + 1)} (hw : w ∈ (D.fiberChart x).target) :
    (D.localChart x).ambientChart ((D.fiberChart x).symm w).1 =
      neatHalfSpaceInclusion (D.localChart x).equiv (D.localChart x).normal_eq w :=
  D.ambientChart_symm_fiberChart x hw

theorem model_symm_inclusionEuclidean
    (L : (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)))
    (hNormal : ∀ u v, (L (u, v)) 0 = u 0)
    {z : EuclideanSpace ℝ (Fin (k + 1))} (hz : z ∈ range (𝓡∂ (k + 1))) :
    (𝓡∂ (d + 1)).symm (inclusionEuclidean L z) =
      neatHalfSpaceInclusion L hNormal ((𝓡∂ (k + 1)).symm z) := by
  apply Subtype.ext
  have hzVal := coe_modelWithCornersEuclideanHalfSpace_symm hz
  have hz0 : 0 ≤ z 0 := by
    simpa [range_modelWithCornersEuclideanHalfSpace] using hz
  have hrange := inclusionEuclidean_mem_range L hNormal hz0
  have hcoe := coe_modelWithCornersEuclideanHalfSpace_symm hrange
  simpa [inclusionEuclidean, neatHalfSpaceInclusion, hzVal] using hcoe

theorem ambient_symm_model_symm_inclusion
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x : S)
    {z : EuclideanSpace ℝ (Fin (k + 1))}
    (hzTarget : (𝓡∂ (k + 1)).symm z ∈ (D.fiberChart x).target)
    (hzRange : z ∈ range (𝓡∂ (k + 1))) :
    (D.localChart x).ambientChart.symm
        ((𝓡∂ (d + 1)).symm (inclusionEuclidean (D.localChart x).equiv z)) =
      ((D.fiberChart x).symm ((𝓡∂ (k + 1)).symm z)).1 := by
  have hinc := D.ambientChart_symm_fiberChart x hzTarget
  have hmodel := model_symm_inclusionEuclidean
    (D.localChart x).equiv (D.localChart x).normal_eq hzRange
  have hsrc : ((D.fiberChart x).symm ((𝓡∂ (k + 1)).symm z)).1 ∈
      (D.localChart x).ambientChart.source :=
    D.fiberChart_source_subset_ambient_source x
      ((D.fiberChart x).symm.map_source hzTarget)
  have hleft := (D.localChart x).ambientChart.left_inv hsrc
  rw [hmodel, ← hinc]
  exact hleft

/-- The extended fiber-chart transition equals the ambient transition of the two
linear neat inclusions. -/
theorem fiberTransition_eqOn
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x y : S) :
    EqOn
      ((𝓡∂ (k + 1)) ∘ ((D.fiberChart x).symm.trans (D.fiberChart y)) ∘
        (𝓡∂ (k + 1)).symm)
      (projectionEuclidean (D.localChart y).equiv ∘
        ((𝓡∂ (d + 1)) ∘
          ((D.localChart x).ambientChart.symm.trans (D.localChart y).ambientChart) ∘
            (𝓡∂ (d + 1)).symm) ∘
        inclusionEuclidean (D.localChart x).equiv)
      ((𝓡∂ (k + 1)).symm ⁻¹'
          ((D.fiberChart x).symm.trans (D.fiberChart y)).source ∩
        range (𝓡∂ (k + 1))) := by
  intro z hz
  have hzFx : (𝓡∂ (k + 1)).symm z ∈ (D.fiberChart x).target := by
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact hz.1.1
  have hzFy : (D.fiberChart x).symm ((𝓡∂ (k + 1)).symm z) ∈
      (D.fiberChart y).source := by
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact hz.1.2
  have hAmbSymm := ambient_symm_model_symm_inclusion D x hzFx hz.2
  have he :
      ((D.fiberChart x).symm.trans (D.fiberChart y)) ((𝓡∂ (k + 1)).symm z) =
        D.fiberChart y ((D.fiberChart x).symm ((𝓡∂ (k + 1)).symm z)) :=
    OpenPartialHomeomorph.trans_apply _ _
  have hyApply :=
    (D.localChart y).pointedSubtypeChart_apply y (D.mem_ambient_source y) hzFy
  have hΦ :
      ((D.localChart x).ambientChart.symm.trans (D.localChart y).ambientChart)
          ((𝓡∂ (d + 1)).symm (inclusionEuclidean (D.localChart x).equiv z)) =
        (D.localChart y).ambientChart
          ((D.fiberChart x).symm ((𝓡∂ (k + 1)).symm z)).1 := by
    rw [OpenPartialHomeomorph.trans_apply, hAmbSymm]
  change
      (((D.fiberChart x).symm.trans (D.fiberChart y)) ((𝓡∂ (k + 1)).symm z)).1 =
        projectionEuclidean (D.localChart y).equiv
          (((D.localChart x).ambientChart.symm.trans
              (D.localChart y).ambientChart)
            ((𝓡∂ (d + 1)).symm (inclusionEuclidean (D.localChart x).equiv z))).1
  rw [he, hΦ]
  have hval := congrArg (fun w : EuclideanHalfSpace (k + 1) ↦ w.1) hyApply
  simpa [fiberChart, projectionEuclidean, neatHalfSpaceProjection] using hval

theorem fiberTransition_mapsTo_ambient
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x y : S) :
    MapsTo (inclusionEuclidean (D.localChart x).equiv)
      ((𝓡∂ (k + 1)).symm ⁻¹'
          ((D.fiberChart x).symm.trans (D.fiberChart y)).source ∩
        range (𝓡∂ (k + 1)))
      ((𝓡∂ (d + 1)).symm ⁻¹'
          ((D.localChart x).ambientChart.symm.trans
            (D.localChart y).ambientChart).source ∩
        range (𝓡∂ (d + 1))) := by
  intro z hz
  have hzFx : (𝓡∂ (k + 1)).symm z ∈ (D.fiberChart x).target := by
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact hz.1.1
  have hzFy : (D.fiberChart x).symm ((𝓡∂ (k + 1)).symm z) ∈
      (D.fiberChart y).source := by
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact hz.1.2
  have hz0 : 0 ≤ z 0 := by
    simpa [range_modelWithCornersEuclideanHalfSpace] using hz.2
  refine ⟨?_, inclusionEuclidean_mem_range (D.localChart x).equiv
    (D.localChart x).normal_eq hz0⟩
  rw [OpenPartialHomeomorph.trans_source]
  have hAmbSymm := ambient_symm_model_symm_inclusion D x hzFx hz.2
  have hmodel := model_symm_inclusionEuclidean
    (D.localChart x).equiv (D.localChart x).normal_eq hz.2
  constructor
  · have hsrc : ((D.fiberChart x).symm ((𝓡∂ (k + 1)).symm z)).1 ∈
        (D.localChart x).ambientChart.source :=
      D.fiberChart_source_subset_ambient_source x
        ((D.fiberChart x).symm.map_source hzFx)
    have hmap := (D.localChart x).ambientChart.map_source hsrc
    change (𝓡∂ (d + 1)).symm (inclusionEuclidean (D.localChart x).equiv z) ∈
      (D.localChart x).ambientChart.target
    rw [hmodel, ← D.ambientChart_symm_fiberChart x hzFx]
    exact hmap
  · have hyAmb := D.fiberChart_source_subset_ambient_source y hzFy
    simpa [hAmbSymm] using hyAmb

/-- Pairwise fiber-chart transitions are `C∞` because they factor as the ambient
transition sandwiched between the linear neat inclusion and projection. -/
theorem fiberTransition_contDiffOn
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x y : S) :
    ContDiffOn ℝ ∞
      ((𝓡∂ (k + 1)) ∘ ((D.fiberChart x).symm.trans (D.fiberChart y)) ∘
        (𝓡∂ (k + 1)).symm)
      ((𝓡∂ (k + 1)).symm ⁻¹'
          ((D.fiberChart x).symm.trans (D.fiberChart y)).source ∩
        range (𝓡∂ (k + 1))) := by
  let Lx := (D.localChart x).equiv
  let Ly := (D.localChart y).equiv
  let Φ := (𝓡∂ (d + 1)) ∘
    ((D.localChart x).ambientChart.symm.trans (D.localChart y).ambientChart) ∘
      (𝓡∂ (d + 1)).symm
  let Ψ := projectionEuclidean Ly ∘ Φ ∘ inclusionEuclidean Lx
  have hΦ : ContDiffOn ℝ ∞ Φ
      ((𝓡∂ (d + 1)).symm ⁻¹'
          ((D.localChart x).ambientChart.symm.trans
            (D.localChart y).ambientChart).source ∩
        range (𝓡∂ (d + 1))) :=
    D.ambientTransition_contDiffOn x y
  have hΨ : ContDiffOn ℝ ∞ Ψ
      (inclusionEuclidean Lx ⁻¹'
        ((𝓡∂ (d + 1)).symm ⁻¹'
            ((D.localChart x).ambientChart.symm.trans
              (D.localChart y).ambientChart).source ∩
          range (𝓡∂ (d + 1)))) := by
    have hIncl : ContDiffOn ℝ ∞ (inclusionEuclidean Lx) Set.univ :=
      (contDiff_inclusionEuclidean Lx).contDiffOn
    have hProj : ContDiffOn ℝ ∞ (projectionEuclidean Ly) Set.univ :=
      (contDiff_projectionEuclidean Ly).contDiffOn
    have hΦ' := hΦ.comp (hIncl.mono (fun _ _ ↦ trivial)) (fun _ hx ↦ hx)
    exact hProj.comp hΦ' (fun _ _ ↦ trivial)
  have hEq := fiberTransition_eqOn D x y
  have hMaps := fiberTransition_mapsTo_ambient D x y
  exact (hΨ.mono (fun z hz ↦ hMaps hz)).congr hEq

theorem fiberChart_compatible
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) (x y : S) :
    (D.fiberChart x).symm.trans (D.fiberChart y) ∈
      contDiffGroupoid ∞ (𝓡∂ (k + 1)) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  refine ⟨fiberTransition_contDiffOn D x y, ?_⟩
  -- The inverse transition is the swapped pair, because
  -- `(e.trans f).symm = f.symm.trans e`.
  simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using
    fiberTransition_contDiffOn D y x

/-- Package a covering family of ambient neat-slice charts as the internal
embedded-chart data used to assemble the `C∞` fiber structure. -/
noncomputable def toEmbeddedChartFamily
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) :
    CInfinityHalfSpaceEmbeddedChartFamily (d := d) (k := k) (q := q) S where
  chart := D.fiberChart
  mem_source := D.mem_fiberChart_source
  compatible := D.fiberChart_compatible
  ambientChart := fun x ↦ (D.localChart x).ambientChart
  ambient_mem_source := D.mem_ambient_source
  ambient_mem_maximalAtlas := fun x ↦ (D.localChart x).ambient_mem_maximalAtlas
  source_subset := D.fiberChart_source_subset
  equiv := fun x ↦ (D.localChart x).equiv
  writtenInExtend := D.writtenInExtend_of_fiberChart
  normal_eq := D.fiberChart_normal_eq_ambient

theorem exists_structure_of_neatSliceFamily
    (D : CInfinityNeatSliceFamily (d := d) (k := k) (q := q) S) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace (k + 1)) S,
      ∃ hs : IsManifold (𝓡∂ (k + 1)) ∞ S,
        let _ : ChartedSpace (EuclideanHalfSpace (k + 1)) S := cs
        let _ : IsManifold (𝓡∂ (k + 1)) ∞ S := hs
        IsSmoothEmbedding (𝓡∂ (k + 1)) (𝓡∂ (d + 1)) ∞
            (Subtype.val : S → M) ∧
          Subtype.val '' (𝓡∂ (k + 1)).boundary S =
            S ∩ (𝓡∂ (d + 1)).boundary M :=
  (toEmbeddedChartFamily D).exists_structure_embedding_and_boundary

end CInfinityNeatSliceFamily

end Family

end Manifold
