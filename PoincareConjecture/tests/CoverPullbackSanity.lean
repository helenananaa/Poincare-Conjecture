import PoincareConjecture
import Mathlib.Analysis.Calculus.Deriv.Abs

open Set Bundle Manifold
open PoincareConjecture.Topology.FiberSaturation
open CoverPullback
open scoped Manifold ContDiff
noncomputable section

-- A genuine sphere cylinder with its usual smooth structure.
def sphereHeight : ℝ × Sphere2 → AddCircle (4 : ℝ) := fun z => z.1

theorem sphereHeight_continuous : Continuous sphereHeight := by
  exact (AddCircle.continuous_mk' (4 : ℝ)).comp continuous_fst

section Sphere
local instance : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 2))) (CircleSpace sphereHeight) :=
  circleChartedSpace sphereHeight sphereHeight_continuous

example : IsManifold ((𝓘(ℝ,ℝ)).prod (𝓡 2)) ∞ (CircleSpace sphereHeight) :=
  circle_isManifold sphereHeight ((𝓘(ℝ,ℝ)).prod (𝓡 2)) sphereHeight_continuous

example : IsLocalDiffeomorph ((𝓘(ℝ,ℝ)).prod (𝓡 2)) ((𝓘(ℝ,ℝ)).prod (𝓡 2)) ∞
    (forget : CircleSpace sphereHeight → ℝ × Sphere2) :=
  circle_forget_isLocalDiffeomorph sphereHeight ((𝓘(ℝ,ℝ)).prod (𝓡 2)) sphereHeight_continuous

example : (CircleSpace sphereHeight) ≃ₘ⟮(𝓘(ℝ,ℝ)).prod (𝓡 2),
    (𝓘(ℝ,ℝ)).prod (𝓡 2)⟯ (CircleSpace sphereHeight) :=
  circleDeckDiffeomorph sphereHeight ((𝓘(ℝ,ℝ)).prod (𝓡 2)) sphereHeight_continuous

example (x : Sphere2) : height (circleDeck sphereHeight ⟨(0,(0,x)),rfl⟩) = (4 : ℝ) := by
  change (0 : ℝ)+4 = 4
  norm_num

example (x : Sphere2) : forget (circleDeck sphereHeight ⟨(0,(0,x)),rfl⟩) = (0,x) := rfl

example (z : CircleSpace sphereHeight) :
    height ((circleDeck sphereHeight).symm z) = height z-4 := rfl

example (z : CircleSpace sphereHeight) : circleDeck sphereHeight z ≠ z := by
  intro h
  have hh := congrArg height h
  rw [circleDeck_height] at hh
  linarith

example : Function.Surjective (forget : CircleSpace sphereHeight → ℝ × Sphere2) :=
  forget_surjective QuotientAddGroup.mk_surjective
end Sphere

-- The original base projection is NOT silently made smooth.
def absHeight : ℝ → AddCircle (4 : ℝ) := fun x => (|x| : ℝ)
theorem absHeight_continuous : Continuous absHeight :=
  (AddCircle.continuous_mk' (4 : ℝ)).comp continuous_abs

section Abs
local instance : ChartedSpace ℝ (CircleSpace absHeight) :=
  circleChartedSpace absHeight absHeight_continuous

def absLift (x : ℝ) : CircleSpace absHeight := ⟨(|x|,x),rfl⟩

theorem absLift_continuous : Continuous absLift :=
  (continuous_abs.prodMk continuous_id).subtype_mk _

theorem absLift_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ absLift :=
  contMDiff_of_localDiffeomorph_comp
    (circle_forget_isLocalDiffeomorph absHeight 𝓘(ℝ,ℝ) absHeight_continuous)
    absLift_continuous contMDiff_id

example : ¬ ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (height : CircleSpace absHeight → ℝ) := by
  intro h
  have hc : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (abs : ℝ → ℝ) := h.comp absLift_smooth
  exact not_differentiableAt_abs_zero (hc.contDiff.differentiable (by simp) 0)
end Abs

-- Native pullback comparison uses the dependent fibers, with no guessed topology.
example {B R F : Type*} (E : B → Type*) (c : R → B)
    [TopologicalSpace R] [TopologicalSpace (TotalSpace F E)] :
    TotalSpace F (c *ᵖ E) ≃ₜ Space c (TotalSpace.proj (F := F) (E := E)) :=
  bundleHomeomorph E c
