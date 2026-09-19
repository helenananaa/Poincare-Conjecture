import PoincareConjecture
import Mathlib.Analysis.Calculus.Deriv.Abs

open Set Bundle Manifold Function
open PoincareConjecture.Topology.FiberSaturation
open scoped Manifold ContDiff
noncomputable section

local instance : ChartedSpace ℝ (AddCircle (4 : ℝ)) := CircleSmooth.chartedSpace 4
local instance : IsManifold 𝓘(ℝ,ℝ) ∞ (AddCircle (4 : ℝ)) := CircleSmooth.isManifold 4

example (t : ℝ) : IsLocalDiffeomorphAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞
    ((↑) : ℝ → AddCircle (4 : ℝ)) t := CircleSmooth.coe_isLocalDiffeomorph 4 t

abbrev SmoothExampleBundle := Bundle.Trivial (AddCircle (4 : ℝ)) Sphere2
abbrev SmoothExampleTotal := TotalSpace Sphere2 SmoothExampleBundle
abbrev sphereProdModel := (𝓘(ℝ,ℝ)).prod (𝓡 2)

-- The native trivial total space uses the ordinary product smooth structure.
local instance : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 2))) SmoothExampleTotal :=
  CoverLift.chartedSpace (Bundle.Trivial.homeomorphProd (AddCircle (4 : ℝ)) Sphere2).isLocalHomeomorph

local instance : IsManifold sphereProdModel ∞ SmoothExampleTotal :=
  CoverLift.isManifold sphereProdModel
    (Bundle.Trivial.homeomorphProd (AddCircle (4 : ℝ)) Sphere2).isLocalHomeomorph

local instance : T2Space SmoothExampleTotal :=
  (Bundle.Trivial.homeomorphProd (AddCircle (4 : ℝ)) Sphere2).symm.t2Space

theorem sphere_standard_chart_smooth : SmoothBundle.IsSmoothBundleChart
    𝓘(ℝ,ℝ) sphereProdModel (𝓡 2)
      (Bundle.Trivial.trivialization (AddCircle (4 : ℝ)) Sphere2) := by
  let e := Bundle.Trivial.homeomorphProd (AddCircle (4 : ℝ)) Sphere2
  have he := CoverLift.isLocalDiffeomorph sphereProdModel e.isLocalHomeomorph
  have hinv : ContMDiff sphereProdModel sphereProdModel ∞ e.symm :=
    contMDiff_of_localDiffeomorph_comp he e.symm.continuous
      (contMDiff_id.congr (fun z => e.apply_symm_apply z))
  exact ⟨he.contMDiff.contMDiffOn,hinv.contMDiffOn⟩

-- Supply only charts restricted to local circle arcs, not a period map.
theorem sphere_local_smooth_atlas : ∀ b : AddCircle (4 : ℝ),
    ∃ k : Trivialization Sphere2 (TotalSpace.proj (F := Sphere2) (E := SmoothExampleBundle)),
      b ∈ k.baseSet ∧ SmoothBundle.IsSmoothBundleChart 𝓘(ℝ,ℝ) sphereProdModel (𝓡 2) k := by
  intro b
  let e := Bundle.Trivial.trivialization (AddCircle (4 : ℝ)) Sphere2
  let A := (CircleSmooth.logChart 4 (CircleSmooth.representative 4 b)).source
  have hA : IsOpen A := (CircleSmooth.logChart 4 (CircleSmooth.representative 4 b)).open_source
  have hb : b ∈ A := mem_chart_source ℝ b
  exact ⟨e.restrOpen A hA,⟨mem_univ _,hb⟩,
    SmoothBundle.isSmoothBundleChart_restrOpen sphere_standard_chart_smooth A hA⟩

-- All outputs of the new presentation theorem are instantiated.
example : ∃ φ : Sphere2 ≃ₘ⟮𝓡 2,𝓡 2⟯ Sphere2,
    ∃ q : Sphere2 × ℝ → SmoothExampleTotal,
      IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ,ℝ)) sphereProdModel ∞ q ∧ Surjective q ∧
      (∀ z : Sphere2 × ℝ, (q z).proj = (z.2 : AddCircle (4 : ℝ))) ∧
      (∀ t : ℝ, Injective (fun x : Sphere2 => q (x,t))) ∧
      (∀ x t, q (x,t+4) = q (φ x,t)) :=
  SmoothBundle.abstract_bundle_smooth_real_presentation SmoothExampleBundle
    (by norm_num) sphere_local_smooth_atlas

-- The smoothness condition on the original base projection is substantive.
example : ¬ ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞
    (fun t : ℝ => ((|t| : ℝ) : AddCircle (4 : ℝ))) := by
  intro h
  have ha : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (abs : ℝ → ℝ) :=
    contMDiff_of_localDiffeomorph_comp (CircleSmooth.coe_isLocalDiffeomorph 4)
      continuous_abs h
  exact not_differentiableAt_abs_zero (ha.contDiff.differentiable (by simp) 0)
