import Mathlib
import LeeSmoothLib.Ch01.Sec01_07.Problem_1_8
import LeeSmoothLib.Ch04.Sec04_26.Definition_4_26_extra_1
universe u v

-- Declarations for this item will be appended below by the statement pipeline.

-- Local API note: semantic `lean_leansearch` was unavailable in this session, so this item uses
-- the existing mathlib notions `IsCoveringMap` and `IsProperMap`; the converse-failure clause is
-- stated directly because importing the current repository example file would pull in unrelated
-- pre-existing errors.

open scoped Manifold ContDiff

namespace Problem4_11

private theorem angleFunction_sub_int_mul_two_pi
    {U : TopologicalSpace.Opens Circle} {θ : U → ℝ}
    (hθ : IsAngleFunction θ) (m : ℤ) :
    IsAngleFunction (fun z ↦ θ z - m * (2 * Real.pi)) := by
  constructor
  · exact hθ.1.sub continuous_const
  · intro z
    calc
      Circle.exp (θ z - m * (2 * Real.pi))
          = Circle.exp (θ z) / Circle.exp (m * (2 * Real.pi)) := by
            rw [Circle.exp_sub]
      _ = Circle.exp (θ z) / 1 := by rw [Circle.exp_int_mul_two_pi]
      _ = Circle.exp (θ z) := by simp
      _ = z := hθ.2 z

private theorem exists_angleFunction_through_exp (x : ℝ) :
    ∃ (U : TopologicalSpace.Opens Circle) (hxU : Circle.exp x ∈ U) (θ : U → ℝ),
      IsAngleFunction θ ∧ θ ⟨Circle.exp x, hxU⟩ = x := by
  let U : TopologicalSpace.Opens Circle :=
    ⟨{z : Circle | z ≠ -Circle.exp x}, isOpen_compl_singleton⟩
  have hxU : Circle.exp x ∈ U := by
    change Circle.exp x ≠ -Circle.exp x
    simpa [eq_comm] using Circle.neg_ne_self (Circle.exp x)
  have hmissing : -Circle.exp x ∉ U := by
    simp [U]
  rcases exists_angleFunction_of_missing_point (U := U) (c := -Circle.exp x) hmissing with
    ⟨θ₀, hθ₀⟩
  let z₀ : U := ⟨Circle.exp x, hxU⟩
  have hθ₀x : Circle.exp (θ₀ z₀) = Circle.exp x := by
    simpa using hθ₀.2 z₀
  rcases Circle.exp_eq_exp.mp hθ₀x with ⟨m, hm⟩
  let θ : U → ℝ := fun z ↦ θ₀ z - m * (2 * Real.pi)
  have hθ : IsAngleFunction θ := angleFunction_sub_int_mul_two_pi hθ₀ m
  refine ⟨U, hxU, θ, hθ, ?_⟩
  have hshift : θ₀ z₀ - m * (2 * Real.pi) = x := by
    linarith
  simpa [θ] using hshift

private noncomputable def angleFunctionExtension
    {U : TopologicalSpace.Opens Circle} (θ : U → ℝ) : Circle → ℝ :=
  let _ : DecidablePred fun z : Circle ↦ z ∈ U := Classical.decPred _
  fun z ↦ if hz : z ∈ U then θ ⟨z, hz⟩ else 0

private noncomputable def angleFunctionPartialDiffeomorph
    {U : TopologicalSpace.Opens Circle} {θ : U → ℝ} (hθ : IsAngleFunction θ) :
    PartialDiffeomorph (𝓘(ℝ)) (𝓡 1) ℝ Circle (∞ : ℕ∞ω) where
  toPartialEquiv :=
    { toFun := Circle.exp
      invFun := angleFunctionExtension θ
      source := hθ.openImage
      target := U
      map_source' := fun {y} hy ↦ hθ.mapsTo_circleExp_openImage hy
      map_target' := by
        intro z hz
        by_cases h : z ∈ U
        · refine ⟨⟨z, h⟩, ?_⟩
          simp [angleFunctionExtension, h]
        · exact (h hz).elim
      left_inv' := by
        intro y hy
        have hyU : Circle.exp y ∈ U := hθ.mapsTo_circleExp_openImage hy
        have hbranch :=
          congrArg (fun f : hθ.openImage → ℝ ↦ f ⟨y, hy⟩)
            hθ.theta_comp_circleExpOpenImage
        simpa [Function.comp, angleFunctionExtension,
          IsAngleFunction.circleExpOpenImage, hyU] using! hbranch
      right_inv' := by
        intro z hz
        by_cases h : z ∈ U
        · simpa [angleFunctionExtension, h] using hθ.2 ⟨z, h⟩
        · exact (h hz).elim }
  open_source := hθ.openImage.2
  open_target := U.2
  contMDiffOn_toFun := by
    simpa using (contMDiff_circleExp).contMDiffOn
  contMDiffOn_invFun := by
    intro z hz
    have hθz :
        ContMDiffAt (I := 𝓡 1) (I' := 𝓘(ℝ)) (n := (∞ : ℕ∞ω))
          (angleFunctionExtension θ) z := by
      rw [← contMDiffAt_subtype_iff
        (U := U)
        (f := angleFunctionExtension θ)
        (x := ⟨z, hz⟩)]
      simpa [angleFunctionExtension] using hθ.contMDiff ⟨z, hz⟩
    exact hθz.contMDiffWithinAt

private theorem circleExp_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓘(ℝ)) (𝓡 1) (∞ : ℕ∞ω) Circle.exp := by
  intro x
  obtain ⟨U, hxU, θ, hθ, hθx⟩ := exists_angleFunction_through_exp x
  refine ⟨angleFunctionPartialDiffeomorph hθ, ?_, ?_⟩
  · change x ∈ hθ.openImage
    exact ⟨⟨Circle.exp x, hxU⟩, hθx⟩
  · intro y _hy
    rfl

end Problem4_11

/-- Problem 4-11 (1): a topological covering map is proper if and only if each of its fibers is
finite. -/
theorem isProperMap_iff_finite_fibers_of_isCoveringMap
    {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X] {π : E → X}
    (hπ : IsCoveringMap π) :
    IsProperMap π ↔ ∀ x, (π ⁻¹' {x}).Finite := by
  constructor
  · intro hproper x
    refine (hproper.isCompact_preimage isCompact_singleton).finite ?_
    exact ⟨(hπ x).discreteTopology_fiber⟩
  · intro hfinite
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    refine ⟨hπ.continuous, ?_, fun x ↦ (hfinite x).isCompact⟩
    classical
    choose U hxU hUopen hpreopen H hH using fun x ↦ (hπ x).2
    let coverSets : X → TopologicalSpace.Opens X := fun x ↦ ⟨U x, hUopen x⟩
    have hcover : TopologicalSpace.IsOpenCover coverSets :=
      TopologicalSpace.IsOpenCover.of_sets hUopen <| Set.eq_univ_of_forall fun x ↦
        Set.mem_iUnion.mpr ⟨x, hxU x⟩
    rw [hcover.isClosedMap_iff_restrictPreimage]
    intro x
    haveI : Fintype (π ⁻¹' {x}) := (hfinite x).fintype
    change IsClosedMap ((U x).restrictPreimage π)
    have heq : (U x).restrictPreimage π = Prod.fst ∘ H x := by
      funext e
      apply Subtype.ext
      exact (hH x e).symm
    rw [heq]
    exact isClosedMap_fst_of_compactSpace.comp (H x).isClosedMap

/-- Problem 4-11 (2): consequently, the converse of Proposition 4.46 is false; there exists a
smooth covering map that is not proper. -/
theorem exists_smoothCoveringMap_not_isProperMap :
    ∃ π : ℝ → Circle, Manifold.IsSmoothCoveringMap (𝓘(ℝ)) (𝓡 1) π ∧ ¬ IsProperMap π := by
  refine ⟨Circle.exp, ?_, ?_⟩
  · exact ⟨Circle.isCoveringMap_exp, Circle.exp_surjective,
      Problem4_11.circleExp_isLocalDiffeomorph⟩
  · intro hproper
    have hfinite :
        (Circle.exp ⁻¹' ({(1 : Circle)} : Set Circle)).Finite :=
      (isProperMap_iff_finite_fibers_of_isCoveringMap Circle.isCoveringMap_exp).mp
        hproper 1
    let multiples : ℤ → ℝ := fun n ↦ n * (2 * Real.pi)
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 :=
      ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
    have hinjective : Function.Injective multiples := by
      intro m n hmn
      have hcast : (m : ℝ) = (n : ℝ) := by
        exact mul_right_cancel₀ htwoPi hmn
      exact_mod_cast hcast
    have hrangeInfinite : (Set.range multiples).Infinite :=
      Set.infinite_range_of_injective hinjective
    have hrangeSubset :
        Set.range multiples ⊆ Circle.exp ⁻¹' ({(1 : Circle)} : Set Circle) := by
      rintro y ⟨n, rfl⟩
      simpa [multiples] using Circle.exp_int_mul_two_pi n
    exact (hrangeInfinite.mono hrangeSubset) hfinite
