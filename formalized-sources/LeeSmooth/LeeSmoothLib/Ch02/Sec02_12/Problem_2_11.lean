import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.IsLocalHomeomorph
import LeeSmoothLib.Ch01.Sec01_04.Example_1_33
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped LinearAlgebra.Projectivization Manifold ContDiff

universe u

variable {n : ℕ}

/-- Precomposing two charts by the same global transport chart cancels from their transition
map. -/
private lemma projectivization_transport_transition_eq
    {X Y H : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace H]
    (eS : OpenPartialHomeomorph X Y)
    {e c : OpenPartialHomeomorph Y H}
    (hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl Y) :
    (eS.trans e).symm.trans (eS.trans c) = e.symm.trans c := by
  calc
    (eS.trans e).symm.trans (eS.trans c)
        = ((e.symm.trans eS.symm).trans eS).trans c := by
            simp [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
              OpenPartialHomeomorph.trans_assoc]
    _ = (e.symm.trans (eS.symm.trans eS)).trans c := by
          rw [← OpenPartialHomeomorph.trans_assoc]
    _ = (e.symm.trans (OpenPartialHomeomorph.refl Y)).trans c := by rw [hmid]
    _ = e.symm.trans c := by simp [OpenPartialHomeomorph.trans_refl]

namespace Projectivization

section BasisEquiv

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V : Type u} [AddCommGroup V] [Module 𝕜 V]

/-- The linear equivalence sending the standard coordinates on `𝕜^(n+1)` to the basis `b` of
`V`. -/
abbrev basisLinearEquiv (b : Module.Basis (Fin (n + 1)) 𝕜 V) :
    EuclideanSpace 𝕜 (Fin (n + 1)) ≃ₗ[𝕜] V :=
  (EuclideanSpace.equiv (Fin (n + 1)) 𝕜).toLinearEquiv.trans b.equivFun.symm

/-- The map on projectivizations induced by the basis `b`. -/
def basisMap (b : Module.Basis (Fin (n + 1)) 𝕜 V) :
    ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) → ℙ 𝕜 V :=
  Projectivization.map (basisLinearEquiv b).toLinearMap (basisLinearEquiv b).injective

/-- The inverse projectivization map induced by the inverse basis equivalence. -/
private def basisMapSymm (b : Module.Basis (Fin (n + 1)) 𝕜 V) :
    ℙ 𝕜 V → ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) :=
  Projectivization.map (basisLinearEquiv b).symm.toLinearMap (basisLinearEquiv b).symm.injective

/-- The basis-induced equivalence between the standard projective space and `ℙ 𝕜 V`. -/
private def basisEquiv (b : Module.Basis (Fin (n + 1)) 𝕜 V) :
    ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) ≃ ℙ 𝕜 V :=
  { toFun := basisMap b
    invFun := basisMapSymm b
    left_inv := fun x ↦ by
      let e := basisLinearEquiv b
      have hcomp :
          basisMapSymm b (basisMap b x) =
            Projectivization.map (e.trans e.symm).toLinearMap (e.trans e.symm).injective x := by
        simpa [basisMap, basisMapSymm, Function.comp, e] using
          congrArg (fun f ↦ f x) <|
            (Projectivization.map_comp
              e.toLinearMap e.injective e.symm.toLinearMap e.symm.injective).symm
      have hid :
          Projectivization.map (e.trans e.symm).toLinearMap (e.trans e.symm).injective = id := by
        ext y
        induction y using ind with
        | h v hv =>
            simp [Projectivization.map_mk, LinearEquiv.self_trans_symm]
      calc
        basisMapSymm b (basisMap b x)
            = Projectivization.map
                (e.trans e.symm).toLinearMap
                (e.trans e.symm).injective x := hcomp
        _ = x := by
          simpa using congrArg (fun f ↦ f x) hid
    right_inv := fun x ↦ by
      let e := basisLinearEquiv b
      have hcomp :
          basisMap b (basisMapSymm b x) =
            Projectivization.map (e.symm.trans e).toLinearMap (e.symm.trans e).injective x := by
        simpa [basisMap, basisMapSymm, Function.comp, e] using
          congrArg (fun f ↦ f x) <|
            (Projectivization.map_comp
              e.symm.toLinearMap e.symm.injective e.toLinearMap e.injective).symm
      have hid :
          Projectivization.map (e.symm.trans e).toLinearMap (e.symm.trans e).injective = id := by
        ext y
        induction y using ind with
        | h v hv =>
            simp [Projectivization.map_mk, LinearEquiv.symm_trans_self]
      calc
        basisMap b (basisMapSymm b x)
            = Projectivization.map
                (e.symm.trans e).toLinearMap
                (e.symm.trans e).injective x := hcomp
        _ = x := by
          simpa using congrArg (fun f ↦ f x) hid }

/-- The canonical bundled diffeomorphism attached to a basis once the forward and inverse
projectivization maps are known to be smooth. -/
private def basisDiffeomorph
    [TopologicalSpace (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    [ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    [IsManifold (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) (⊤ : ℕ∞ω)
      (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    [TopologicalSpace (ℙ 𝕜 V)]
    [ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 V)]
    [IsManifold (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) (⊤ : ℕ∞ω) (ℙ 𝕜 V)]
    (b : Module.Basis (Fin (n + 1)) 𝕜 V)
    (h_to : ContMDiff (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n)))
      (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) ∞ (basisMap b))
    (h_inv : ContMDiff (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n)))
      (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) ∞ (basisMapSymm b)) :
    ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) ≃ₘ⟮𝓘(ℝ, EuclideanSpace 𝕜 (Fin n)),
      𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))⟯ ℙ 𝕜 V where
  toEquiv := basisEquiv b
  contMDiff_toFun := h_to
  contMDiff_invFun := h_inv

end BasisEquiv

section Real

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

private abbrev topologicalSpaceOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V) :
    TopologicalSpace (ℙ ℝ V) :=
  (basisEquiv b).symm.topologicalSpace

/-- The transported basis homeomorphism is defined on all of `ℙ ℝ V`. -/
private theorem basisHomeomorph_source_univ (b : Module.Basis (Fin (n + 1)) ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    (((basisEquiv b).symm.homeomorph).toOpenPartialHomeomorph).source = Set.univ := by
  simp [Homeomorph.toOpenPartialHomeomorph]

/-- Transport a standard chart on `ℝP[n]` across the basis homeomorphism. -/
private def chartOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V)
    (e : OpenPartialHomeomorph ℝP[n] (EuclideanSpace ℝ (Fin n))) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    OpenPartialHomeomorph (ℙ ℝ V) (EuclideanSpace ℝ (Fin n)) :=
  let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
  ((basisEquiv b).symm.homeomorph).toOpenPartialHomeomorph.trans e

private abbrev chartedSpaceOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) :=
  let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
  let eS : OpenPartialHomeomorph (ℙ ℝ V) (ℝP[n]) :=
    ((basisEquiv b).symm.homeomorph).toOpenPartialHomeomorph
  let _ : ChartedSpace (ℝP[n]) (ℙ ℝ V) :=
    OpenPartialHomeomorph.singletonChartedSpace (e := eS) (basisHomeomorph_source_univ b)
  ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) (ℝP[n]) (ℙ ℝ V)

private theorem isManifoldOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    let _ : @ChartedSpace (EuclideanSpace ℝ (Fin n)) _ (ℙ ℝ V) (topologicalSpaceOfBasis b) :=
      chartedSpaceOfBasis b
    IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := by
  letI : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
  let eS : OpenPartialHomeomorph (ℙ ℝ V) (ℝP[n]) :=
    ((basisEquiv b).symm.homeomorph).toOpenPartialHomeomorph
  let hS : eS.source = Set.univ := basisHomeomorph_source_univ b
  letI : ChartedSpace (ℝP[n]) (ℙ ℝ V) :=
    OpenPartialHomeomorph.singletonChartedSpace (e := eS) hS
  letI : @ChartedSpace (EuclideanSpace ℝ (Fin n)) _ (ℙ ℝ V)
      (topologicalSpaceOfBasis b) := chartedSpaceOfBasis b
  have hGroupoid : HasGroupoid (ℙ ℝ V) (contDiffGroupoid (⊤ : ℕ∞ω) (𝓡 n)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa using OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq (e := eS) hS f hf
    have hf'Eq : f' = eS := by
      simpa using OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq (e := eS) hS f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl (ℝP[n]) := by
      ext x <;> simp [eS]
    have hcMax : c ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : ℕ∞ω) (ℝP[n]) :=
      IsManifold.subset_maximalAtlas (I := 𝓡 n) (n := (⊤ : ℕ∞ω)) hc
    have hc'Max : c' ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : ℕ∞ω) (ℝP[n]) :=
      IsManifold.subset_maximalAtlas (I := 𝓡 n) (n := (⊤ : ℕ∞ω)) hc'
    have hcompat : c.symm.trans c' ∈ contDiffGroupoid (⊤ : ℕ∞ω) (𝓡 n) :=
      IsManifold.compatible_of_mem_maximalAtlas hcMax hc'Max
    have htransport : (eS.trans c).symm.trans (eS.trans c') = c.symm.trans c' := by
      simpa using projectivization_transport_transition_eq (eS := eS) (e := c) (c := c') hmid
    rw [htransport]
    exact hcompat
  exact IsManifold.mk' (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V)

/-- In the singleton intermediate charted space, the preferred chart is the transported basis
homeomorphism at every point. -/
private theorem basisIntermediateChartAt_eq
    (b : Module.Basis (Fin (n + 1)) ℝ V) (y : ℙ ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    let _ : ChartedSpace (ℝP[n]) (ℙ ℝ V) :=
      OpenPartialHomeomorph.singletonChartedSpace
        (e := ((basisEquiv b).symm.homeomorph).toOpenPartialHomeomorph)
        (basisHomeomorph_source_univ b)
    chartAt (ℝP[n]) y = ((basisEquiv b).symm.homeomorph).toOpenPartialHomeomorph := by
  simp [OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq]

/-- The chosen-basis map is smooth into the manifold structure transported along that basis. -/
private theorem basisMap_contMDiff (b : Module.Basis (Fin (n + 1)) ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := chartedSpaceOfBasis b
    let _ : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := isManifoldOfBasis b
    ContMDiff (𝓡 n) (𝓡 n) ∞ (basisMap b) := by
  let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
  let eS : OpenPartialHomeomorph (ℙ ℝ V) (ℝP[n]) :=
    ((basisEquiv b).symm.homeomorph).toOpenPartialHomeomorph
  let _ : ChartedSpace (ℝP[n]) (ℙ ℝ V) :=
    OpenPartialHomeomorph.singletonChartedSpace (e := eS) (basisHomeomorph_source_univ b)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := chartedSpaceOfBasis b
  let _ : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := isManifoldOfBasis b
  change ContMDiff (𝓡 n) (𝓡 n) ∞ (basisMap b)
  intro x
  rw [contMDiffAt_iff]
  constructor
  · simpa [eS, basisMapSymm] using!
      (((basisEquiv b).symm.homeomorph).continuous_invFun.continuousAt :
        ContinuousAt (basisMap b) x)
  · have hchart : chartAt (ℝP[n]) (basisMap b x) = eS := by
      simpa [eS] using basisIntermediateChartAt_eq b (basisMap b x)
    have hpoint : eS (basisMap b x) = x := by
      change basisMapSymm b (basisMap b x) = x
      exact (basisEquiv b).left_inv x
    have hcenter :
        letI := ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) (ℝP[n]) (ℙ ℝ V)
        extChartAt (𝓡 n) (basisMap b x) (basisMap b x) = extChartAt (𝓡 n) x x := by
      simpa [extChartAt_comp, chartAt_comp, hchart, hpoint,
        OpenPartialHomeomorph.trans_apply]
    have hcenterChart :
        letI := ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) (ℝP[n]) (ℙ ℝ V)
        chartAt (EuclideanSpace ℝ (Fin n)) (basisMap b x) (basisMap b x) =
          chartAt (EuclideanSpace ℝ (Fin n)) x x := by
      simpa [chartAt_comp, hchart, hpoint, OpenPartialHomeomorph.trans_apply]
    refine
      (contDiffWithinAt_id :
        ContDiffWithinAt ℝ ∞
          (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (Set.range (𝓡 n)) (extChartAt (𝓡 n) x x)).congr_of_eventuallyEq_of_mem ?_ ?_
    · have htarget :
          letI := ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) (ℝP[n]) (ℙ ℝ V)
          (extChartAt (𝓡 n) (basisMap b x)).target ∈
            nhdsWithin (extChartAt (𝓡 n) x x) (Set.range (𝓡 n)) := by
        have htarget' :
            letI := ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) (ℝP[n]) (ℙ ℝ V)
            (extChartAt (𝓡 n) (basisMap b x)).target ∈
              nhdsWithin (extChartAt (𝓡 n) (basisMap b x) (basisMap b x))
                (Set.range (𝓡 n)) := by
          exact extChartAt_target_mem_nhdsWithin (I := 𝓡 n) (basisMap b x)
        simpa [hcenter, hcenterChart] using htarget'
      filter_upwards [htarget] with y hy
      simpa [hchart, hpoint, eS, basisMapSymm] using!
        (writtenInExtChartAt_chartAt_symm_comp
          (I := 𝓡 n) (H := EuclideanSpace ℝ (Fin n)) (H' := ℝP[n])
          (x := basisMap b x) (y := y) hy)
    · exact Set.mem_of_subset_of_mem (extChartAt_target_subset_range (I := 𝓡 n) x)
        (mem_extChartAt_target (I := 𝓡 n) x)

/-- The inverse chosen-basis map is smooth back to the standard real projective space. -/
private theorem basisMapSymm_contMDiff (b : Module.Basis (Fin (n + 1)) ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := chartedSpaceOfBasis b
    let _ : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := isManifoldOfBasis b
    ContMDiff (𝓡 n) (𝓡 n) ∞ (basisMapSymm b) := by
  let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
  let eS : OpenPartialHomeomorph (ℙ ℝ V) (ℝP[n]) :=
    ((basisEquiv b).symm.homeomorph).toOpenPartialHomeomorph
  let _ : ChartedSpace (ℝP[n]) (ℙ ℝ V) :=
    OpenPartialHomeomorph.singletonChartedSpace (e := eS) (basisHomeomorph_source_univ b)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := chartedSpaceOfBasis b
  let _ : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := isManifoldOfBasis b
  change ContMDiff (𝓡 n) (𝓡 n) ∞ (basisMapSymm b)
  intro x
  rw [contMDiffAt_iff]
  constructor
  · simpa [eS, basisMapSymm] using!
      (((basisEquiv b).symm.homeomorph).continuous_toFun.continuousAt :
        ContinuousAt (basisMapSymm b) x)
  · have hchart : chartAt (ℝP[n]) x = eS := by
      simpa [eS] using basisIntermediateChartAt_eq b x
    refine
      (contDiffWithinAt_id :
        ContDiffWithinAt ℝ ∞
          (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (Set.range (𝓡 n)) (extChartAt (𝓡 n) x x)).congr_of_eventuallyEq_of_mem ?_ ?_
    · filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓡 n) x] with y hy
      simpa [hchart, eS, basisMapSymm] using!
        (writtenInExtChartAt_chartAt_comp
          (I := 𝓡 n) (H := EuclideanSpace ℝ (Fin n)) (H' := ℝP[n])
          (x := x) (y := y) hy)
    · exact Set.mem_of_subset_of_mem (extChartAt_target_subset_range (I := 𝓡 n) x)
        (mem_extChartAt_target (I := 𝓡 n) x)

/-- The chosen basis gives a diffeomorphism from standard projective space to the transported
manifold. -/
private def basisTransportDiffeomorph (b : Module.Basis (Fin (n + 1)) ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := chartedSpaceOfBasis b
    let _ : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := isManifoldOfBasis b
    ℝP[n] ≃ₘ⟮𝓡 n, 𝓡 n⟯ ℙ ℝ V :=
  let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := chartedSpaceOfBasis b
  let _ : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := isManifoldOfBasis b
  { toEquiv := basisEquiv b
    contMDiff_toFun := basisMap_contMDiff b
    contMDiff_invFun := basisMapSymm_contMDiff b }

end Real

end Projectivization

namespace Projectivization

/-- A smooth structure on `ℙ 𝕜 V` is basis-compatible if every basis-induced map from the
standard projective space `ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))` extends to the canonical
basis-induced diffeomorphism for that ambient manifold structure, and if `V` actually admits
an `(n + 1)`-indexed basis. This is the source-facing basis-independence condition used for the
real and complex projectivization problems in this section. -/
def BasisCompatible (n : ℕ) {𝕜 : Type*} [RCLike 𝕜] (V : Type u) [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    [ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    [IsManifold (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) (⊤ : ℕ∞ω)
      (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    (t : TopologicalSpace (ℙ 𝕜 V))
    (c : let _ : TopologicalSpace (ℙ 𝕜 V) := t
      ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 V))
    (m : let _ : TopologicalSpace (ℙ 𝕜 V) := t
      let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 V) := c
      IsManifold (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) (⊤ : ℕ∞ω) (ℙ 𝕜 V)) : Prop :=
  let _ : TopologicalSpace (ℙ 𝕜 V) := t
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 V) := c
  let _ : IsManifold (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) (⊤ : ℕ∞ω) (ℙ 𝕜 V) := m
  let I := 𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))
  ∃ _ : Module.Basis (Fin (n + 1)) 𝕜 V,
    ∀ b : Module.Basis (Fin (n + 1)) 𝕜 V,
      ∃ Φ : ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) ≃ₘ⟮I, I⟯ ℙ 𝕜 V,
        ∀ x, Φ x = basisMap b x

/-- A standard real-projective affine chart is a member of the smooth maximal atlas. -/
private theorem realProjectiveChart_mem_maximalAtlas_for_basis_change
    (i : Fin (n + 1)) :
    realProjectiveChart n i ∈ IsManifold.maximalAtlas (𝓡 n) ∞ (ℝP[n]) := by
  have hAtlas :
      realProjectiveChart n i ∈ atlas (EuclideanSpace ℝ (Fin n)) (ℝP[n]) := by
    change realProjectiveChart n i ∈
      {e | ∃ j : Fin (n + 1), e = realProjectiveChart n j}
    exact ⟨i, rfl⟩
  exact IsManifold.subset_maximalAtlas hAtlas

/-- The affine-coordinate formula for the projectivization of a real linear automorphism. -/
private theorem realLinearEquiv_projective_chart_formula
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (i j : Fin (n + 1)) (u : EuclideanSpace ℝ (Fin n)) :
    realProjectiveChart n j
        (Projectivization.map e.toLinearMap e.injective ((realProjectiveChart n i).symm u)) =
      WithLp.toLp 2
        (fun k ↦
          e (realProjectiveChartInvVector n i u) (j.succAbove k) /
            e (realProjectiveChartInvVector n i u) j) := by
  have hv : e (realProjectiveChartInvVector n i u) ≠ 0 := by
    intro hzero
    exact realProjectiveChartInvVector_ne_zero n i u <| e.injective (by simpa using hzero)
  rw [realProjectiveChart_symm_apply, Projectivization.map_mk]
  simpa [EuclideanSpace.equiv] using
    (realProjectiveChart_mk n j (e (realProjectiveChartInvVector n i u)) hv)

/-- The image of an affine representative lies in a target projective chart exactly when the
corresponding transformed homogeneous coordinate is nonzero. -/
private theorem realLinearEquiv_projective_image_mem_chartDomain_iff
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (i j : Fin (n + 1)) (u : EuclideanSpace ℝ (Fin n)) :
    Projectivization.map e.toLinearMap e.injective ((realProjectiveChart n i).symm u) ∈
        realProjectiveChartDomain n j ↔
      e (realProjectiveChartInvVector n i u) j ≠ 0 := by
  have hv : e (realProjectiveChartInvVector n i u) ≠ 0 := by
    intro hzero
    exact realProjectiveChartInvVector_ne_zero n i u <| e.injective (by simpa using hzero)
  rw [realProjectiveChart_symm_apply, Projectivization.map_mk]
  simpa using
    (realProjectiveChartDomain_mk n j (e (realProjectiveChartInvVector n i u)) hv)

/-- Applying a fixed real linear automorphism to the inserted homogeneous representative is a
smooth Euclidean-space map. -/
private theorem realLinearEquiv_projective_coordinate_contDiff
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (i l : Fin (n + 1)) :
    ContDiff ℝ ∞
      (fun u : EuclideanSpace ℝ (Fin n) ↦ e (realProjectiveChartInvVector n i u) l) := by
  have hInv : ContDiff ℝ ∞ (realProjectiveChartInvVector n i) := by
    refine contDiff_piLp' (p := (2 : ENNReal)) ?_
    intro q
    exact (realProjectiveChartInvVector_coordinate_contDiff n i q).of_le (by simp)
  have hImage :
      ContDiff ℝ ∞
        (fun u : EuclideanSpace ℝ (Fin n) ↦ e (realProjectiveChartInvVector n i u)) := by
    simpa using! e.toContinuousLinearEquiv.contDiff.comp hInv
  simpa [Function.comp] using!
    ((contDiff_piLp_apply (p := (2 : ENNReal)) (i := l)) :
      ContDiff ℝ ∞
        (fun v : EuclideanSpace ℝ (Fin (n + 1)) ↦ v l)).comp hImage

/-- The quotient-of-coordinates expression for a projective linear automorphism is smooth at
each point where its target-chart denominator is nonzero. -/
private theorem realLinearEquiv_projective_localModel_contDiffWithinAt
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) {u₀ : EuclideanSpace ℝ (Fin n)} {j : Fin (n + 1)}
    (hj : e (realProjectiveChartInvVector n i u₀) j ≠ 0) :
    ContDiffWithinAt ℝ ∞
      (fun u : EuclideanSpace ℝ (Fin n) ↦
        WithLp.toLp 2
          (fun k ↦
            e (realProjectiveChartInvVector n i u) (j.succAbove k) /
              e (realProjectiveChartInvVector n i u) j))
      (Set.range (𝓡 n)) u₀ := by
  refine contDiffWithinAt_piLp' (p := (2 : ENNReal)) ?_
  intro k
  exact
    (realLinearEquiv_projective_coordinate_contDiff e i (j.succAbove k)).contDiffWithinAt.div
      (realLinearEquiv_projective_coordinate_contDiff e i j).contDiffWithinAt hj

/-- On the target of an extended source chart, the written projective-linear map agrees with its
explicit quotient-of-coordinates formula. -/
private theorem realLinearEquiv_projective_chartExpression_eventuallyEq
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {x : ℝP[n]} (i j : Fin (n + 1)) (hx : x ∈ realProjectiveChartDomain n i) :
    let f : ℝP[n] → ℝP[n] := fun z ↦ Projectivization.map e.toLinearMap e.injective z
    let φ := realProjectiveChart n i
    let ψ := realProjectiveChart n j
    let x' : EuclideanSpace ℝ (Fin n) := (φ.extend (𝓡 n)) x
    ((ψ.extend (𝓡 n)) ∘ f ∘ (φ.extend (𝓡 n)).symm)
      =ᶠ[nhdsWithin x' (Set.range (𝓡 n))]
        (fun u : EuclideanSpace ℝ (Fin n) ↦
          WithLp.toLp 2
            (fun k ↦
              e (realProjectiveChartInvVector n i u) (j.succAbove k) /
                e (realProjectiveChartInvVector n i u) j)) := by
  let f : ℝP[n] → ℝP[n] := fun z ↦ Projectivization.map e.toLinearMap e.injective z
  let φ := realProjectiveChart n i
  let ψ := realProjectiveChart n j
  let x' : EuclideanSpace ℝ (Fin n) := (φ.extend (𝓡 n)) x
  have hxsource : x ∈ φ.source := by simpa [φ] using! hx
  have htarget : (φ.extend (𝓡 n)).target ∈ nhdsWithin x' (Set.range (𝓡 n)) := by
    simpa [φ, x'] using (φ.extend_target_mem_nhdsWithin (I := 𝓡 n) hxsource)
  refine Filter.eventuallyEq_of_mem htarget ?_
  intro u hu
  simpa [φ, ψ, Function.comp, OpenPartialHomeomorph.extend_coe_symm,
    OpenPartialHomeomorph.extend_coe] using
      realLinearEquiv_projective_chart_formula e i j u

/-- A projectivized real linear automorphism is continuous for the quotient topology on standard
real projective space. -/
private theorem realLinearEquiv_projectivization_continuous
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    Continuous (fun x : ℝP[n] ↦ Projectivization.map e.toLinearMap e.injective x) := by
  let P :
      {v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0} →
        {v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0} :=
    fun v ↦ ⟨e v, by
      intro hzero
      exact v.2 <| e.injective (by simpa using hzero)⟩
  have hP : Continuous P := by
    exact (e.toContinuousLinearEquiv.continuous.comp continuous_subtype_val).subtype_mk fun v ↦ by
      intro hzero
      exact v.2 <| e.injective (by simpa using hzero)
  let q : {v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0} → ℝP[n] :=
    Projectivization.mk' ℝ
  have hq : Continuous q := by
    simpa [q, Projectivization.mk'] using!
      (continuous_quotient_mk' :
        Continuous
          (@Quotient.mk'
            {v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0}
            (projectivizationSetoid ℝ (EuclideanSpace ℝ (Fin (n + 1))))))
  have hmk :
      Continuous
        (fun v : {v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0} ↦
          Projectivization.mk ℝ (e v) (P v).2) := by
    simpa [q, P, Projectivization.mk'_eq_mk] using! hq.comp hP
  simpa [Projectivization.map, Projectivization.lift, P] using!
    hmk.quotient_lift fun a b hab ↦ by
      rcases (show ∃ c : ℝˣ,
          c • (b : EuclideanSpace ℝ (Fin (n + 1))) =
            (a : EuclideanSpace ℝ (Fin (n + 1))) from by
        simpa [projectivizationSetoid, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
          using! hab) with ⟨c, hc⟩
      exact
        (Projectivization.mk_eq_mk_iff ℝ (e a) (e b) (P a).2 (P b).2).2
          ⟨c, by
            calc
              c • e (b : EuclideanSpace ℝ (Fin (n + 1))) =
                  e (c • (b : EuclideanSpace ℝ (Fin (n + 1)))) :=
                    (e.map_smul c (b : EuclideanSpace ℝ (Fin (n + 1)))).symm
              _ = e (a : EuclideanSpace ℝ (Fin (n + 1))) := by rw [hc]⟩

/-- A real linear automorphism of homogeneous coordinates induces a smooth self-map of standard
real projective space. -/
private theorem realLinearEquiv_projectivization_contMDiff
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    ContMDiff (𝓡 n) (𝓡 n) ∞
      (fun x : ℝP[n] ↦ Projectivization.map e.toLinearMap e.injective x) := by
  let f : ℝP[n] → ℝP[n] :=
    fun x ↦ Projectivization.map e.toLinearMap e.injective x
  intro x
  obtain ⟨i, hx⟩ := real_projective_space_has_standard_chart n x
  obtain ⟨j, hy⟩ := real_projective_space_has_standard_chart n (f x)
  let φ := realProjectiveChart n i
  let ψ := realProjectiveChart n j
  let x' : EuclideanSpace ℝ (Fin n) := (φ.extend (𝓡 n)) x
  have hφ : φ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ (ℝP[n]) :=
    realProjectiveChart_mem_maximalAtlas_for_basis_change i
  have hψ : ψ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ (ℝP[n]) :=
    realProjectiveChart_mem_maximalAtlas_for_basis_change j
  have hxsource : x ∈ φ.source := by simpa [φ] using! hx
  have hysource : f x ∈ ψ.source := by simpa [ψ] using! hy
  rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas
    (I := 𝓡 n) (I' := 𝓡 n) (e := φ) (e' := ψ) hφ hψ hxsource hysource,
    continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
  refine ⟨(realLinearEquiv_projectivization_continuous e).continuousAt, ?_⟩
  have hxEq : (realProjectiveChart n i).symm x' = x := by
    change (realProjectiveChart n i).symm
      (((realProjectiveChart n i).extend (𝓡 n)) x) = x
    simpa [OpenPartialHomeomorph.extend_coe] using
      (OpenPartialHomeomorph.left_inv (realProjectiveChart n i) hx)
  have hyChart :
      Projectivization.map e.toLinearMap e.injective ((realProjectiveChart n i).symm x') ∈
        realProjectiveChartDomain n j := by
    simpa [f, hxEq] using hy
  have hden : e (realProjectiveChartInvVector n i x') j ≠ 0 :=
    (realLinearEquiv_projective_image_mem_chartDomain_iff e i j x').1 hyChart
  have hmodel := realLinearEquiv_projective_localModel_contDiffWithinAt e i hden
  have hEq := realLinearEquiv_projective_chartExpression_eventuallyEq e i j hx
  have hx'Target : x' ∈ (φ.extend (𝓡 n)).target :=
    (φ.extend (𝓡 n)).map_source <| by
      simpa [φ, OpenPartialHomeomorph.extend_source] using hxsource
  have hx'Range : x' ∈ Set.range (𝓡 n) := φ.extend_target_subset_range hx'Target
  have hEq' := hEq
  exact hmodel.congr_of_eventuallyEq hEq' (hEq'.eq_of_nhdsWithin hx'Range)

private theorem realLinearEquiv_projectivization_left_inv
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    Function.LeftInverse
      (fun x : ℝP[n] ↦ Projectivization.map e.symm.toLinearMap e.symm.injective x)
      (fun x : ℝP[n] ↦ Projectivization.map e.toLinearMap e.injective x) := by
  intro x
  have hcomp :
      Projectivization.map e.symm.toLinearMap e.symm.injective
          (Projectivization.map e.toLinearMap e.injective x) =
        Projectivization.map (e.trans e.symm).toLinearMap (e.trans e.symm).injective x := by
    simpa [Function.comp] using
      congrArg (fun f ↦ f x) <|
        (Projectivization.map_comp
          e.toLinearMap e.injective e.symm.toLinearMap e.symm.injective).symm
  have hid :
      Projectivization.map (e.trans e.symm).toLinearMap (e.trans e.symm).injective = id := by
    ext y
    induction y using Projectivization.ind with
    | h v hv => simp [Projectivization.map_mk, LinearEquiv.self_trans_symm]
  calc
    Projectivization.map e.symm.toLinearMap e.symm.injective
        (Projectivization.map e.toLinearMap e.injective x) =
      Projectivization.map (e.trans e.symm).toLinearMap
        (e.trans e.symm).injective x := hcomp
    _ = x := by simpa using congrArg (fun f ↦ f x) hid

private theorem realLinearEquiv_projectivization_right_inv
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    Function.RightInverse
      (fun x : ℝP[n] ↦ Projectivization.map e.symm.toLinearMap e.symm.injective x)
      (fun x : ℝP[n] ↦ Projectivization.map e.toLinearMap e.injective x) := by
  intro x
  have hcomp :
      Projectivization.map e.toLinearMap e.injective
          (Projectivization.map e.symm.toLinearMap e.symm.injective x) =
        Projectivization.map (e.symm.trans e).toLinearMap (e.symm.trans e).injective x := by
    simpa [Function.comp] using
      congrArg (fun f ↦ f x) <|
        (Projectivization.map_comp
          e.symm.toLinearMap e.symm.injective e.toLinearMap e.injective).symm
  have hid :
      Projectivization.map (e.symm.trans e).toLinearMap (e.symm.trans e).injective = id := by
    ext y
    induction y using Projectivization.ind with
    | h v hv => simp [Projectivization.map_mk, LinearEquiv.symm_trans_self]
  calc
    Projectivization.map e.toLinearMap e.injective
        (Projectivization.map e.symm.toLinearMap e.symm.injective x) =
      Projectivization.map (e.symm.trans e).toLinearMap
        (e.symm.trans e).injective x := hcomp
    _ = x := by simpa using congrArg (fun f ↦ f x) hid

/-- A real linear automorphism induces a diffeomorphism of standard real projective space. -/
private def realLinearEquiv_projectivization_diffeomorph
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    ℝP[n] ≃ₘ⟮𝓡 n, 𝓡 n⟯ ℝP[n] :=
  { toEquiv :=
      { toFun := fun x ↦ Projectivization.map e.toLinearMap e.injective x
        invFun := fun x ↦ Projectivization.map e.symm.toLinearMap e.symm.injective x
        left_inv := realLinearEquiv_projectivization_left_inv e
        right_inv := realLinearEquiv_projectivization_right_inv e }
    contMDiff_toFun := realLinearEquiv_projectivization_contMDiff e
    contMDiff_invFun := realLinearEquiv_projectivization_contMDiff e.symm }

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- Changing from an arbitrary basis to the chosen base basis factors the corresponding basis map
through a projective linear automorphism of standard real projective space. -/
private theorem basisMap_eq_baseBasis_comp_projectivization
    (b₀ b : Module.Basis (Fin (n + 1)) ℝ V) :
    let A : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
      (basisLinearEquiv b).trans (basisLinearEquiv b₀).symm
    basisMap b = basisMap b₀ ∘ Projectivization.map A.toLinearMap A.injective := by
  let A : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (basisLinearEquiv b).trans (basisLinearEquiv b₀).symm
  ext x
  induction x using Projectivization.ind with
  | h v hv => simp [basisMap, Projectivization.map_mk]

private theorem basisCompatible_ofBasis (b₀ : Module.Basis (Fin (n + 1)) ℝ V) :
    BasisCompatible n V (topologicalSpaceOfBasis b₀) (chartedSpaceOfBasis b₀)
      (isManifoldOfBasis b₀) := by
  let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b₀
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := chartedSpaceOfBasis b₀
  let _ : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := isManifoldOfBasis b₀
  refine ⟨b₀, ?_⟩
  intro b
  let A : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (basisLinearEquiv b).trans (basisLinearEquiv b₀).symm
  let Φ : ℝP[n] ≃ₘ⟮𝓡 n, 𝓡 n⟯ ℙ ℝ V :=
    (realLinearEquiv_projectivization_diffeomorph A).trans (basisTransportDiffeomorph b₀)
  refine ⟨Φ, ?_⟩
  intro x
  simpa [Φ, A] using!
    (congrArg (fun f : ℝP[n] → ℙ ℝ V ↦ f x)
      (basisMap_eq_baseBasis_comp_projectivization b₀ b)).symm

end Projectivization

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- Problem 2-11: if `V` is a real vector space of dimension `n + 1`, then `ℙ ℝ V` carries a
basis-compatible smooth structure modeled on `ℝ^n`; any basis-induced map `ℝP[n] → ℙ ℝ V` is a
diffeomorphism. The public owner is the ambient topological, charted, and manifold structure on
`ℙ ℝ V`; the chosen-basis transport used to construct those instances remains internal. -/
theorem real_projectivization_exists_basisCompatible_smoothStructure
    (hn : Module.finrank ℝ V = n + 1) :
    ∃ t : TopologicalSpace (ℙ ℝ V),
      ∃ c : let _ : TopologicalSpace (ℙ ℝ V) := t
        ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V),
      ∃ m : let _ : TopologicalSpace (ℙ ℝ V) := t
          let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := c
          IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V),
          Projectivization.BasisCompatible n V t c m := by
  haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_eq_succ hn
  let b := Module.finBasisOfFinrankEq ℝ V hn
  let t : TopologicalSpace (ℙ ℝ V) := Projectivization.topologicalSpaceOfBasis b
  let c : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) :=
    Projectivization.chartedSpaceOfBasis b
  let m : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := Projectivization.isManifoldOfBasis b
  refine ⟨t, c, m, ?_⟩
  letI : TopologicalSpace (ℙ ℝ V) := t
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := c
  letI : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := m
  simpa [b, t, c, m] using Projectivization.basisCompatible_ofBasis b
