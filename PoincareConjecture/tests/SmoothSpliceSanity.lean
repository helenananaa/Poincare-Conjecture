import PoincareConjecture
import Mathlib.Analysis.Calculus.Deriv.Abs

open Set Bundle Manifold
open PoincareConjecture.Topology.FiberSaturation
open SmoothBundle
open scoped Manifold ContDiff
noncomputable section

/-- A standard product bundle chart, not an assumed global trivialization. -/
def spliceProductChart (F : Type*) [TopologicalSpace F] :
    Trivialization F (Prod.fst : ℝ × F → ℝ) where
  toOpenPartialHomeomorph := (Homeomorph.refl (ℝ × F)).toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := by simp
  proj_toFun _ _ := rfl

theorem spliceProductChart_smooth : IsSmoothTrivialization
    ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (spliceProductChart ℝ) :=
  ⟨contMDiff_id.contMDiffOn,contMDiff_id.contMDiffOn⟩

/-- This time-dependent shear is invertible with its given inverse. -/
def spliceShear : (ℝ × ℝ) ≃ₘ⟮(𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ),
    (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)⟯ (ℝ × ℝ) where
  toFun z := (z.1,z.2+z.1)
  invFun z := (z.1,z.2-z.1)
  left_inv _ := by simp
  right_inv _ := by simp
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_fst)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_fst)

def spliceShearChart : Trivialization ℝ (Prod.fst : ℝ × ℝ → ℝ) :=
  adjust (spliceProductChart ℝ) spliceShear (fun _ => rfl)

theorem spliceShearChart_smooth : IsSmoothTrivialization
    ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) spliceShearChart :=
  isSmooth_adjust spliceProductChart_smooth _ _

-- The input charts do not agree away from the cut.
example : spliceShearChart (1,0) ≠ spliceProductChart ℝ (1,0) := by
  change ((1,0+1) : ℝ × ℝ) ≠ (1,0)
  norm_num

-- Genuine local charts on a two-set cover, neither covering [-3,3].
def spliceLeft := (spliceProductChart ℝ).restrOpen (Iio (1 : ℝ)) isOpen_Iio
def spliceRight := spliceShearChart.restrOpen (Ioi (-1 : ℝ)) isOpen_Ioi

example : ∃ k : Trivialization ℝ (Prod.fst : ℝ × ℝ → ℝ),
    IsSmoothTrivialization ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) k ∧
      Icc (-3 : ℝ) 3 ⊆ k.baseSet := by
  apply exists_smooth_trivialization_Icc continuous_fst
  intro t
  by_cases ht : t < 1
  · refine ⟨spliceLeft,⟨mem_univ _,ht⟩,?_⟩
    exact isSmooth_restrOpen spliceProductChart_smooth _ _
  · refine ⟨spliceRight,⟨mem_univ _,?_⟩,?_⟩
    · change (-1 : ℝ) < t
      linarith
    · exact isSmooth_restrOpen spliceShearChart_smooth _ _

-- Real sphere fibers, retaining the standard smooth sphere model.
example : ∃ k : Trivialization Sphere2 (Prod.fst : ℝ × Sphere2 → ℝ),
    IsSmoothTrivialization ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 2) k ∧
      Icc (-2 : ℝ) 5 ⊆ k.baseSet := by
  apply exists_smooth_trivialization_Icc continuous_fst
  intro t
  exact ⟨spliceProductChart Sphere2,mem_univ _,
    contMDiff_id.contMDiffOn,contMDiff_id.contMDiffOn⟩

example : seamClamp 0 1 (1/2) = (1/2 : ℝ) :=
  seamClamp_eq_self (by norm_num) (by constructor <;> norm_num)

example : seamClamp 0 1 3 = (0 : ℝ) :=
  seamClamp_eq_center (by norm_num) (Or.inr (by norm_num))

-- Merely agreeing at the seam is insufficient: the naive paste is abs.
example : ¬ ContDiff ℝ ∞ (fun t : ℝ => if t ≤ 0 then -t else t) := by
  have heq : (fun t : ℝ => if t ≤ 0 then -t else t) = abs := by
    funext t
    by_cases ht : t ≤ 0
    · simp [ht,abs_of_nonpos ht]
    · simp [ht,abs_of_pos (lt_of_not_ge ht)]
  rw [heq]
  intro h
  exact not_differentiableAt_abs_zero (h.differentiable (by simp) 0)

def spliceCorrected := matchNear spliceProductChart_smooth spliceShearChart_smooth
  (c := 0) (d := 1) (by norm_num)
  (fun _ _ => ⟨mem_univ _,mem_univ _⟩)

-- This computes the actual nontrivial corrected map, keeping t unchanged.
example (t x : ℝ) : spliceCorrected (t,x) = (t,x+t-seamClamp 0 1 t) := rfl

example : spliceCorrected ((1/2 : ℝ),0) = ((1/2 : ℝ),0) := by
  change ((1/2,0+1/2-seamClamp 0 1 (1/2)) : ℝ × ℝ) = (1/2,0)
  rw [seamClamp_eq_self (by norm_num) (by constructor <;> norm_num)]
  norm_num

example : spliceCorrected (3,0) = ((3,3) : ℝ × ℝ) := by
  change ((3,0+3-seamClamp 0 1 3) : ℝ × ℝ) = (3,3)
  rw [seamClamp_eq_center (by norm_num) (Or.inr (by norm_num))]
  norm_num
