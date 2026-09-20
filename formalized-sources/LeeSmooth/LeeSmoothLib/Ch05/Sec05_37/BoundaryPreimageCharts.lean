import Mathlib.Geometry.Manifold.Diffeomorph
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5
import LeeSmoothLib.Ch05.Sec05_37.BoundaryRegularPreimageLinear
import LeeSmoothLib.Ch05.Sec05_37.CInfinityNeatSliceAtlas
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3

/-!
# Local inverse-function-theorem charts for Problem 5-23

Interior points of a standard half-space manifold see an ordinary Euclidean neighbourhood in
extended charts, so the inverse function theorem applies there directly.
-/

open Set Classical
open scoped ContDiff Manifold Topology

noncomputable section

namespace Manifold.BoundaryPreimageCharts

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

theorem extChartAt_target_mem_nhds_of_interior (p : M) (hp : (𝓡∂ (n + 1)).IsInteriorPoint p) :
    (extChartAt (𝓡∂ (n + 1)) p).target ∈ 𝓝 (extChartAt (𝓡∂ (n + 1)) p p) := by
  rw [← nhdsWithin_eq_nhds.2 (range_mem_nhds_isInteriorPoint hp)]
  exact extChartAt_target_mem_nhdsWithin (I := 𝓡∂ (n + 1)) p

/-- Choose an ordinary Euclidean open neighbourhood of an interior point inside the extended
chart target. -/
def interiorChartTarget (p : M) (hp : (𝓡∂ (n + 1)).IsInteriorPoint p) : Set Eₙ :=
  Classical.choose <| mem_nhds_iff.mp (extChartAt_target_mem_nhds_of_interior p hp)

theorem interiorChartTarget_spec (p : M) (hp : (𝓡∂ (n + 1)).IsInteriorPoint p) :
    interiorChartTarget p hp ⊆ (extChartAt (𝓡∂ (n + 1)) p).target ∧
      IsOpen (interiorChartTarget p hp) ∧
        extChartAt (𝓡∂ (n + 1)) p p ∈ interiorChartTarget p hp :=
  Classical.choose_spec <| mem_nhds_iff.mp (extChartAt_target_mem_nhds_of_interior p hp)

theorem interiorChartTarget_subset (p : M) (hp : (𝓡∂ (n + 1)).IsInteriorPoint p) :
    interiorChartTarget p hp ⊆ (extChartAt (𝓡∂ (n + 1)) p).target :=
  (interiorChartTarget_spec p hp).1

theorem isOpen_interiorChartTarget (p : M) (hp : (𝓡∂ (n + 1)).IsInteriorPoint p) :
    IsOpen (interiorChartTarget p hp) :=
  (interiorChartTarget_spec p hp).2.1

theorem mem_interiorChartTarget (p : M) (hp : (𝓡∂ (n + 1)).IsInteriorPoint p) :
    extChartAt (𝓡∂ (n + 1)) p p ∈ interiorChartTarget p hp :=
  (interiorChartTarget_spec p hp).2.2

/-- Source of the restricted interior chart. -/
def interiorChartSource (p : M) (hp : (𝓡∂ (n + 1)).IsInteriorPoint p) : Set M :=
  (extChartAt (𝓡∂ (n + 1)) p).source ∩ extChartAt (𝓡∂ (n + 1)) p ⁻¹' interiorChartTarget p hp

theorem isOpen_interiorChartSource (p : M) (hp : (𝓡∂ (n + 1)).IsInteriorPoint p) :
    IsOpen (interiorChartSource p hp) :=
  (continuousOn_extChartAt (I := 𝓡∂ (n + 1)) p).isOpen_inter_preimage
    (isOpen_extChartAt_source (I := 𝓡∂ (n + 1)) p) (isOpen_interiorChartTarget p hp)

/-- Restricted extended chart at an interior point, as a partial equivalence with open Euclidean
target. -/
def interiorChartPartialEquiv (p : M) (hp : (𝓡∂ (n + 1)).IsInteriorPoint p) : PartialEquiv M Eₙ :=
  (extChartAt (𝓡∂ (n + 1)) p).restr (interiorChartSource p hp)

theorem interiorChartPartialEquiv_target (p : M) (hp : (𝓡∂ (n + 1)).IsInteriorPoint p) :
    (interiorChartPartialEquiv p hp).target = interiorChartTarget p hp := by
  ext y
  constructor
  · intro hy
    have hy' : y ∈ (extChartAt (𝓡∂ (n + 1)) p).target ∩
        (extChartAt (𝓡∂ (n + 1)) p).symm ⁻¹' interiorChartSource p hp := by
      simpa [interiorChartPartialEquiv] using hy
    have hySrc : (extChartAt (𝓡∂ (n + 1)) p).symm y ∈ interiorChartSource p hp := hy'.2
    have hyU : extChartAt (𝓡∂ (n + 1)) p ((extChartAt (𝓡∂ (n + 1)) p).symm y) ∈
        interiorChartTarget p hp := hySrc.2
    have hyEq : extChartAt (𝓡∂ (n + 1)) p ((extChartAt (𝓡∂ (n + 1)) p).symm y) = y :=
      (extChartAt (𝓡∂ (n + 1)) p).right_inv hy'.1
    rwa [hyEq] at hyU
  · intro hyU
    have hyT : y ∈ (extChartAt (𝓡∂ (n + 1)) p).target :=
      interiorChartTarget_subset p hp hyU
    have hsymm : (extChartAt (𝓡∂ (n + 1)) p).symm y ∈ (extChartAt (𝓡∂ (n + 1)) p).source :=
      (extChartAt (𝓡∂ (n + 1)) p).map_target hyT
    have hpre : extChartAt (𝓡∂ (n + 1)) p ((extChartAt (𝓡∂ (n + 1)) p).symm y) ∈
        interiorChartTarget p hp := by
      rwa [(extChartAt (𝓡∂ (n + 1)) p).right_inv hyT]
    exact ⟨hyT, ⟨hsymm, hpre⟩⟩

theorem mem_interiorChartSource (p : M) (hp : (𝓡∂ (n + 1)).IsInteriorPoint p) :
    p ∈ interiorChartSource p hp :=
  ⟨mem_extChartAt_source (I := 𝓡∂ (n + 1)) p, mem_interiorChartTarget p hp⟩

theorem euclideanHalfSpace_eq_subtype (k : ℕ) [NeZero k] :
    EuclideanHalfSpace k = {x : EuclideanSpace ℝ (Fin k) // 0 ≤ x 0} :=
  rfl

/-- Restrict a Euclidean open partial homeomorphism that preserves the closed half-space to a
partial homeomorphism of `EuclideanHalfSpace`. -/
def restrictToHalfSpace {k : ℕ} [NeZero k]
    (Ψ : OpenPartialHomeomorph
      (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)))
    (hsrc : ∀ z ∈ Ψ.source, 0 ≤ z 0 → 0 ≤ Ψ z 0)
    (htgt : ∀ z ∈ Ψ.target, 0 ≤ z 0 → 0 ≤ Ψ.symm z 0) :
    OpenPartialHomeomorph (EuclideanHalfSpace k) (EuclideanHalfSpace k) where
  toFun z :=
    if hz : z.1 ∈ Ψ.source then ⟨Ψ z.1, hsrc z.1 hz z.2⟩ else 0
  invFun z :=
    if hz : z.1 ∈ Ψ.target then ⟨Ψ.symm z.1, htgt z.1 hz z.2⟩ else 0
  source := {z | z.1 ∈ Ψ.source}
  target := {z | z.1 ∈ Ψ.target}
  map_source' := by
    intro z hz
    change z.1 ∈ Ψ.source at hz
    simp only [hz, ↓reduceDIte]
    exact Ψ.map_source hz
  map_target' := by
    intro z hz
    change z.1 ∈ Ψ.target at hz
    simp only [hz, ↓reduceDIte]
    exact Ψ.map_target hz
  left_inv' := by
    intro z hz
    change z.1 ∈ Ψ.source at hz
    have hmap : Ψ z.1 ∈ Ψ.target := Ψ.map_source hz
    simp only [hz, hmap, ↓reduceDIte]
    apply EuclideanHalfSpace.ext
    exact Ψ.left_inv hz
  right_inv' := by
    intro z hz
    change z.1 ∈ Ψ.target at hz
    have hmap : Ψ.symm z.1 ∈ Ψ.source := Ψ.map_target hz
    simp only [hz, hmap, ↓reduceDIte]
    apply EuclideanHalfSpace.ext
    exact Ψ.right_inv hz
  open_source :=
    (Ψ.open_source.preimage
      (continuous_subtype_val : Continuous (fun z : EuclideanHalfSpace k ↦ z.1)))
  open_target :=
    (Ψ.open_target.preimage
      (continuous_subtype_val : Continuous (fun z : EuclideanHalfSpace k ↦ z.1)))
  continuousOn_toFun := by
    have hval : Continuous (fun z : EuclideanHalfSpace k ↦ z.1) := continuous_subtype_val
    have hcomp : ContinuousOn (fun z : EuclideanHalfSpace k ↦ Ψ z.1)
        {z | z.1 ∈ Ψ.source} :=
      Ψ.continuousOn.comp hval.continuousOn fun _ hz ↦ hz
    rw [continuousOn_iff_continuous_restrict]
    refine continuous_induced_rng.2 ?_
    change Continuous fun z : {z : EuclideanHalfSpace k | z.1 ∈ Ψ.source} ↦
      (if hz : z.1.1 ∈ Ψ.source then
          (⟨Ψ z.1.1, hsrc z.1.1 hz z.1.2⟩ : EuclideanHalfSpace k)
        else (0 : EuclideanHalfSpace k)).1
    have hEq : (fun z : {z : EuclideanHalfSpace k | z.1 ∈ Ψ.source} ↦
        (if hz : z.1.1 ∈ Ψ.source then
            (⟨Ψ z.1.1, hsrc z.1.1 hz z.1.2⟩ : EuclideanHalfSpace k)
          else (0 : EuclideanHalfSpace k)).1) =
        fun z ↦ Ψ z.1.1 := by
      funext z
      have hz : z.1.1 ∈ Ψ.source := z.property
      simp [hz]
    rw [hEq]
    exact continuousOn_iff_continuous_restrict.mp hcomp
  continuousOn_invFun := by
    have hval : Continuous (fun z : EuclideanHalfSpace k ↦ z.1) := continuous_subtype_val
    have hcomp : ContinuousOn (fun z : EuclideanHalfSpace k ↦ Ψ.symm z.1)
        {z | z.1 ∈ Ψ.target} :=
      Ψ.continuousOn_symm.comp hval.continuousOn fun _ hz ↦ hz
    rw [continuousOn_iff_continuous_restrict]
    refine continuous_induced_rng.2 ?_
    change Continuous fun z : {z : EuclideanHalfSpace k | z.1 ∈ Ψ.target} ↦
      (if hz : z.1.1 ∈ Ψ.target then
          (⟨Ψ.symm z.1.1, htgt z.1.1 hz z.1.2⟩ : EuclideanHalfSpace k)
        else (0 : EuclideanHalfSpace k)).1
    have hEq : (fun z : {z : EuclideanHalfSpace k | z.1 ∈ Ψ.target} ↦
        (if hz : z.1.1 ∈ Ψ.target then
            (⟨Ψ.symm z.1.1, htgt z.1.1 hz z.1.2⟩ : EuclideanHalfSpace k)
          else (0 : EuclideanHalfSpace k)).1) =
        fun z ↦ Ψ.symm z.1.1 := by
      funext z
      have hz : z.1.1 ∈ Ψ.target := z.property
      simp [hz]
    rw [hEq]
    exact continuousOn_iff_continuous_restrict.mp hcomp

theorem restrictToHalfSpace_source {k : ℕ} [NeZero k]
    (Ψ : OpenPartialHomeomorph
      (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)))
    (hsrc : ∀ z ∈ Ψ.source, 0 ≤ z 0 → 0 ≤ Ψ z 0)
    (htgt : ∀ z ∈ Ψ.target, 0 ≤ z 0 → 0 ≤ Ψ.symm z 0) :
    (restrictToHalfSpace Ψ hsrc htgt).source = {z | z.1 ∈ Ψ.source} :=
  rfl

theorem restrictToHalfSpace_apply {k : ℕ} [NeZero k]
    (Ψ : OpenPartialHomeomorph
      (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)))
    (hsrc : ∀ z ∈ Ψ.source, 0 ≤ z 0 → 0 ≤ Ψ z 0)
    (htgt : ∀ z ∈ Ψ.target, 0 ≤ z 0 → 0 ≤ Ψ.symm z 0)
    {z : EuclideanHalfSpace k} (hz : z.1 ∈ Ψ.source) :
    restrictToHalfSpace Ψ hsrc htgt z = ⟨Ψ z.1, hsrc z.1 hz z.2⟩ := by
  simp [restrictToHalfSpace, hz]

/-- Preservation of the closed half-space is automatic if source and target lie in the open
half-space. -/
theorem halfSpace_preserved_of_subset_interior {k : ℕ} [NeZero k]
    (Ψ : OpenPartialHomeomorph
      (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)))
    (hsrc : Ψ.source ⊆ {z | 0 < z 0})
    (htgt : Ψ.target ⊆ {z | 0 < z 0}) :
    (∀ z ∈ Ψ.source, 0 ≤ z 0 → 0 ≤ Ψ z 0) ∧
      (∀ z ∈ Ψ.target, 0 ≤ z 0 → 0 ≤ Ψ.symm z 0) := by
  constructor
  · intro z hz _
    exact le_of_lt (htgt (Ψ.map_source hz))
  · intro z hz _
    exact le_of_lt (hsrc (Ψ.map_target hz))

/-- Preservation of the closed half-space is automatic if the Euclidean map keeps coordinate `0`. -/
theorem halfSpace_preserved_of_coord_zero {k : ℕ} [NeZero k]
    (Ψ : OpenPartialHomeomorph
      (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)))
    (hΨ : ∀ z ∈ Ψ.source, Ψ z 0 = z 0)
    (hΨsymm : ∀ z ∈ Ψ.target, Ψ.symm z 0 = z 0) :
    (∀ z ∈ Ψ.source, 0 ≤ z 0 → 0 ≤ Ψ z 0) ∧
      (∀ z ∈ Ψ.target, 0 ≤ z 0 → 0 ≤ Ψ.symm z 0) := by
  constructor
  · intro z hz hz0
    rw [hΨ z hz]
    exact hz0
  · intro z hz hz0
    rw [hΨsymm z hz]
    exact hz0

/-- Affine translation of a linear equivalence, as a diffeomorphism of model spaces. -/
def centeredLinearDiffeomorph
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (a : E) : E ≃ₘ[ℝ] F where
  toEquiv :=
    { toFun := fun x ↦ e (x - a)
      invFun := fun y ↦ e.symm y + a
      left_inv := by intro x; simp
      right_inv := by intro y; simp }
  contMDiff_toFun :=
    (e.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff
  contMDiff_invFun :=
    (e.symm.contDiff.add contDiff_const).contMDiff


end Manifold.BoundaryPreimageCharts
