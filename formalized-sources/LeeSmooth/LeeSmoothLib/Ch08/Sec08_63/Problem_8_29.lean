import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch08.Sec08_57.Definition_8_57_extra_1
import LeeSmoothLib.Ch08.Sec08_59.Proposition_8_30
import LeeSmoothLib.Ch08.Sec08_60.Corollary_8_38
import LeeSmoothLib.Ch08.Sec08_60.Notation_8_60_extra_6
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_38
import LeeSmoothLib.Ch05.Sec05_35.Corollary_5_39
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch07.Sec07_47.Example_7_4
import LeeSmoothLib.Ch07.Sec07_49.Definition_7_49_extra_1
import LeeSmoothLib.Ch07.Sec07_50.Example_7_27
import LeeSmoothLib.Ch07.Sec07_53.Problem_7_4
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContDiff ContMDiffMonoidMorphism Manifold Matrix MatrixGroups
open AffineEquiv LinearMap.GeneralLinearGroup Matrix.UnitaryGroup
open Matrix.SpecialLinearGroup

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "Mℝ(" n ")" => Matrix (Fin n) (Fin n) ℝ
local notation "Mℂ(" n ")" => Matrix (Fin n) (Fin n) ℂ
local notation "Iℝ(" n ")" => 𝓘(ℝ, Mℝ(n))
local notation "Iℂ(" n ")" => 𝓘(ℂ, Mℂ(n))
local notation "Iℝℂ(" n ")" => 𝓘(ℝ, Mℂ(n))
local notation "O(" n ")" => Matrix.orthogonalGroup (Fin n) ℝ
local notation "SO(" n ")" => Matrix.specialOrthogonalGroup (Fin n) ℝ
local notation "U(" n ")" => Matrix.unitaryGroup (Fin n) ℂ
local notation "SU(" n ")" => Matrix.specialUnitaryGroup (Fin n) ℂ

local instance
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ∞ G] :
    LieGroup I (minSmoothness 𝕜 3) G :=
  LieGroup.of_le <| show minSmoothness 𝕜 3 ≤ (∞ : ℕ∞ω) by
    have hthree_le_inf : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      decide
    simpa [minSmoothness] using hthree_le_inf

namespace ContMDiffMonoidMorphism

/-- Helper for Problem 8-29: the derivative of a smooth monoid homomorphism at the identity lands
in the target group Lie algebra because `F 1 = 1`. -/
theorem inducedLieAlgebraTargetLinearMapEq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    (GroupLieAlgebra I G →ₗ[𝕜] TangentSpace J (F 1)) =
      (GroupLieAlgebra I G →ₗ[𝕜] GroupLieAlgebra J H) := by
  simpa [GroupLieAlgebra] using!
    congrArg (fun h : H ↦ GroupLieAlgebra I G →ₗ[𝕜] TangentSpace J h) F.map_one

/-- Helper for Problem 8-29: the identity derivative of a smooth monoid homomorphism viewed as a
linear map between the source and target group Lie algebras. -/
noncomputable def inducedLieAlgebraLinearMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    GroupLieAlgebra I G →ₗ[𝕜] GroupLieAlgebra J H :=
  Eq.mp (inducedLieAlgebraTargetLinearMapEq F) (mfderiv I J F (1 : G)).toLinearMap

/-- Evaluating `inducedLieAlgebraLinearMap` is just evaluating `mfderiv I J F 1`, with the
codomain transport collapsed. -/
theorem inducedLieAlgebraLinearMap_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) :
    inducedLieAlgebraLinearMap F X = (mfderiv I J F (1 : G)) X := by
  unfold inducedLieAlgebraLinearMap
  change
    cast (by
      simpa [GroupLieAlgebra] using congrArg (fun h : H ↦ TangentSpace J h) F.map_one)
      ((mfderiv I J F (1 : G)) X) = (mfderiv I J F (1 : G)) X
  exact eq_of_heq (cast_heq _ _)

/-- Helper for Problem 8-29: differentiating the multiplicativity identity
`F ∘ (g * ·) = ((F g) * ·) ∘ F` shows that the pushforward of a left-invariant vector field is
the left-invariant field determined by the derivative at the identity. -/
theorem inducedLieAlgebraLinearMap_mulInvariantVectorField_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) (g : G) :
    mfderiv I J F g (mulInvariantVectorField X g) =
      mulInvariantVectorField (inducedLieAlgebraLinearMap F X) (F g) := by
  have hmin : minSmoothness 𝕜 3 ≠ 0 :=
    lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hF : MDifferentiableAt I J F g :=
    F.contMDiff_toFun.mdifferentiableAt (by simp)
  have hF_one : MDifferentiableAt I J F (1 : G) :=
    F.contMDiff_toFun.mdifferentiableAt (by simp)
  have hmulG : MDifferentiableAt I I (g * ·) (1 : G) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hmin
  have hmulH : MDifferentiableAt J J ((F g) * ·) (1 : H) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hmin
  have hcomp :
      F ∘ (g * ·) = ((F g) * ·) ∘ F := by
    ext x
    simp [map_mul]
  have hsource :
      mfderiv I J F g (mulInvariantVectorField X g) =
        mfderiv I J (F ∘ (g * ·)) (1 : G) X := by
    simpa [mulInvariantVectorField] using
      (mfderiv_comp_apply_of_eq (1 : G) hF hmulG (mul_one g) X).symm
  have hmiddle :
      mfderiv I J (F ∘ (g * ·)) (1 : G) X =
        mfderiv I J (((F g) * ·) ∘ F) (1 : G) X := by
    have hmf :
        @Eq (EG →L[𝕜] EH) (mfderiv I J (F ∘ (g * ·)) (1 : G))
          (mfderiv I J (((F g) * ·) ∘ F) (1 : G)) := by
      simpa [hcomp] using mfderiv_congr hcomp
    simpa using! congrArg (fun L : EG →L[𝕜] EH ↦ L X) hmf
  have htarget :
      mfderiv I J (((F g) * ·) ∘ F) (1 : G) X =
        mfderiv J J ((F g) * ·) (1 : H) ((mfderiv I J F (1 : G)) X) := by
    simpa using!
      mfderiv_comp_apply_of_eq (1 : G) hmulH hF_one F.map_one X
  have htransport :
      mfderiv J J ((F g) * ·) (1 : H) ((mfderiv I J F (1 : G)) X) =
        mulInvariantVectorField (inducedLieAlgebraLinearMap F X) (F g) := by
    rw [mulInvariantVectorField, inducedLieAlgebraLinearMap_apply]
  exact hsource.trans (hmiddle.trans (htarget.trans htransport))

/-- Helper for Problem 8-29: the left-invariant field determined by the identity derivative of a
smooth monoid homomorphism is `F`-related to the original left-invariant field. -/
theorem inducedLieAlgebraLinearMap_related
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) :
    VectorField.f_related F Xᴸ ((inducedLieAlgebraLinearMap F X)ᴸ) := by
  refine ⟨F.contMDiff_toFun, ?_⟩
  intro g
  simpa using inducedLieAlgebraLinearMap_mulInvariantVectorField_apply F X g

/-- Helper for Problem 8-29: once the bracket fields are known to be `F`-related, evaluating at
the identity gives the Lie-bracket compatibility of the derivative-at-identity map. -/
theorem inducedLieAlgebraLinearMap_map_lie_of_related
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G)
    (hBracket :
      VectorField.f_related F
        (VectorField.mlieBracket I (Xᴸ) (Yᴸ))
        (VectorField.mlieBracket J
          ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ))) :
    inducedLieAlgebraLinearMap F ⁅X, Y⁆ =
      ⁅inducedLieAlgebraLinearMap F X, inducedLieAlgebraLinearMap F Y⁆ := by
  have hApply := VectorField.f_related_apply hBracket (1 : G)
  have hBasepoint :
      VectorField.mlieBracket J
          ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (F 1) =
        VectorField.mlieBracket J
          ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (1 : H) := by
    simpa using!
      congrArg
        (fun z : H ↦
          VectorField.mlieBracket J
            ((inducedLieAlgebraLinearMap F X)ᴸ)
            ((inducedLieAlgebraLinearMap F Y)ᴸ) z)
        F.map_one
  simpa [GroupLieAlgebra.bracket_def, inducedLieAlgebraLinearMap_apply] using
    hApply.trans hBasepoint

/-- Helper for Problem 8-29: the derivative-at-identity map preserves brackets because invariant
vector fields and the manifold Lie bracket are natural under `f_related`. -/
theorem inducedLieAlgebraLinearMap_mlieBracket_related_of_applyOne
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G)
    (hBracketAt :
      mfderiv I J F (1 : G) (VectorField.mlieBracket I Xᴸ Yᴸ (1 : G)) =
        VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (1 : H)) :
    VectorField.f_related F
      (VectorField.mlieBracket I Xᴸ Yᴸ)
      (VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
        ((inducedLieAlgebraLinearMap F Y)ᴸ)) := by
  have hBracketElem :
      inducedLieAlgebraLinearMap F ⁅X, Y⁆ =
        ⁅inducedLieAlgebraLinearMap F X, inducedLieAlgebraLinearMap F Y⁆ := by
    -- Read the identity-point bracket computation as an equality in the two group Lie algebras.
    simpa [GroupLieAlgebra.bracket_def, inducedLieAlgebraLinearMap_apply] using hBracketAt
  have hSourceField :
      (⁅X, Y⁆)ᴸ = VectorField.mlieBracket I Xᴸ Yᴸ := by
    -- The bracket of invariant vector fields is the invariant field of the bracket value at `1`.
    simpa [GroupLieAlgebra.bracket_def] using mulInvariantVector_mlieBracket X Y
  have hTargetField :
      (⁅inducedLieAlgebraLinearMap F X, inducedLieAlgebraLinearMap F Y⁆)ᴸ =
        VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ) := by
    -- Apply the same invariant-field identification after pushing both generators forward.
    simpa [GroupLieAlgebra.bracket_def] using
      mulInvariantVector_mlieBracket
        (inducedLieAlgebraLinearMap F X) (inducedLieAlgebraLinearMap F Y)
  refine ⟨F.contMDiff_toFun, ?_⟩
  intro g
  -- Rewrite both bracket fields as invariant fields, then use the already-proved pushforward
  -- formula for invariant vector fields.
  calc
    mfderiv I J F g (VectorField.mlieBracket I Xᴸ Yᴸ g)
        = mfderiv I J F g ((⁅X, Y⁆)ᴸ g) := by
            rw [hSourceField]
    _ = (inducedLieAlgebraLinearMap F ⁅X, Y⁆)ᴸ (F g) := by
          simpa using inducedLieAlgebraLinearMap_mulInvariantVectorField_apply F ⁅X, Y⁆ g
    _ = (⁅inducedLieAlgebraLinearMap F X, inducedLieAlgebraLinearMap F Y⁆)ᴸ (F g) := by
          rw [hBracketElem]
    _ =
        VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (F g) := by
            rw [hTargetField]

/- Helper for Problem 8-29: at the identity, `mfderiv I J F 1` should send the source manifold
bracket of invariant fields to the target manifold bracket of the pushed-forward invariant
fields. -/
section BracketAtOneChartHelpers

universe u𝕜 uEG uHG uG uEH uHH uH

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
variable {H : Type uH} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
variable [LieGroup I ∞ G] [LieGroup J ∞ H]

/-- Helper for Problem 8-29: the preferred-chart expression of `F` at the identity is `C^∞`
within the source chart target. -/
theorem inducedLieAlgebraChartMapContDiffWithinAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let G' := ψ ∘ F ∘ φ.symm
    ContDiffWithinAt 𝕜 ∞ G' φ.target (φ (1 : G)) := by
  -- Compose the source chart inverse, the smooth homomorphism `F`, and the target chart.
  dsimp
  have hFAt : ContMDiffAt I J ∞ F (1 : G) :=
    F.contMDiff_toFun.contMDiffAt
  have hSymm :
      ContMDiffWithinAt 𝓘(𝕜, EG) I ∞
        (extChartAt I (1 : G)).symm
        (extChartAt I (1 : G)).target
        ((extChartAt I (1 : G)) (1 : G)) := by
    exact
      (contMDiffWithinAt_extChartAt_symm_range_self (1 : G)).mono
        (extChartAt_target_subset_range (1 : G))
  have hComp :
      ContMDiffWithinAt 𝓘(𝕜, EG) J ∞
        (F ∘ (extChartAt I (1 : G)).symm)
        (extChartAt I (1 : G)).target
        ((extChartAt I (1 : G)) (1 : G)) := by
    exact hFAt.comp_contMDiffWithinAt_of_eq hSymm (by simp)
  have hChartAt : ContMDiffAt J 𝓘(𝕜, EH) ∞ (extChartAt J (1 : H)) (1 : H) :=
    contMDiffAt_extChartAt
  have hChart :
      ContMDiffWithinAt 𝓘(𝕜, EG) 𝓘(𝕜, EH) ∞
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (extChartAt I (1 : G)).target
        ((extChartAt I (1 : G)) (1 : G)) := by
    exact hChartAt.comp_contMDiffWithinAt_of_eq hComp (by simp)
  -- Convert the manifold statement to the chart-level `ContDiffWithinAt` statement.
  exact hChart.contDiffWithinAt

/-- Helper for Problem 8-29: the source preferred-chart pullback of a left-invariant vector field
is differentiable within `range I` at the chart point of `1`. -/
theorem sourceMulInvariantChartPullbackDifferentiableWithinAtOne
    (Z : GroupLieAlgebra I G) :
    DifferentiableWithinAt 𝕜
      (VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Zᴸ (Set.range I))
      (Set.range I) ((extChartAt I (1 : G)) (1 : G)) := by
  -- Reuse the general chart-pullback differentiability theorem for the invariant field `Zᴸ`.
  have hZAt : MDifferentiableAt I I.tangent (T% Zᴸ) (1 : G) :=
    mdifferentiableAt_mulInvariantVectorField Z
  have hZ : MDifferentiableWithinAt I I.tangent (T% Zᴸ) Set.univ (1 : G) :=
    hZAt.mdifferentiableWithinAt
  simpa using hZ.differentiableWithinAt_mpullbackWithin_vectorField

/-- Helper for Problem 8-29: the target preferred-chart pullback of a left-invariant vector field
is differentiable within `range J` at the chart point of `1`. -/
theorem targetMulInvariantChartPullbackDifferentiableWithinAtOne
    (Z : GroupLieAlgebra J H) :
    DifferentiableWithinAt 𝕜
      (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm Zᴸ (Set.range J))
      (Set.range J) ((extChartAt J (1 : H)) (1 : H)) := by
  -- Reuse the same chart-pullback differentiability theorem on the target Lie group.
  have hZAt : MDifferentiableAt J J.tangent (T% Zᴸ) (1 : H) :=
    mdifferentiableAt_mulInvariantVectorField Z
  have hZ : MDifferentiableWithinAt J J.tangent (T% Zᴸ) Set.univ (1 : H) :=
    hZAt.mdifferentiableWithinAt
  simpa using hZ.differentiableWithinAt_mpullbackWithin_vectorField

/-- Helper for Problem 8-29: near the preferred source chart of `1`, the map
`x ↦ F ((extChartAt I 1).symm x)` stays in the source of the preferred target chart at `1`. -/
theorem chartMapEventuallyIntoTargetSourceAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    (fun x : EG ↦ F ((extChartAt I (1 : G)).symm x)) ⁻¹' (extChartAt J (1 : H)).source ∈
      nhdsWithin ((extChartAt I (1 : G)) (1 : G)) (Set.range I) := by
  -- Compose continuity of `F` at `1` with continuity of the preferred source chart inverse.
  have hFContinuous := F.contMDiff_toFun.continuous
  have hChartLeftInv :
      (extChartAt I (1 : G)).symm ((extChartAt I (1 : G)) (1 : G)) = (1 : G) := by
    simpa using (extChartAt I (1 : G)).left_inv (mem_extChartAt_source (1 : G))
  have hFcont :
      ContinuousAt F ((extChartAt I (1 : G)).symm ((extChartAt I (1 : G)) (1 : G))) := by
    simpa [hChartLeftInv] using! hFContinuous.continuousAt
  have hSymmCont :
      ContinuousAt (extChartAt I (1 : G)).symm
        ((extChartAt I (1 : G)) (1 : G)) :=
    continuousAt_extChartAt_symm (1 : G)
  have hcont :
      ContinuousAt (fun x : EG ↦ F ((extChartAt I (1 : G)).symm x))
        ((extChartAt I (1 : G)) (1 : G)) :=
    hFcont.comp hSymmCont
  have hTargetSourceOne : (extChartAt J (1 : H)).source ∈ nhds (1 : H) :=
    extChartAt_source_mem_nhds (1 : H)
  have hTargetSource : (extChartAt J (1 : H)).source ∈ nhds (F (1 : G)) := by
    simpa [F.map_one] using hTargetSourceOne
  have hTargetSource' :
      (extChartAt J (1 : H)).source ∈
        nhds (F ((extChartAt I (1 : G)).symm ((extChartAt I (1 : G)) (1 : G)))) := by
    simpa [hChartLeftInv] using hTargetSource
  exact nhdsWithin_le_nhds <| hcont.preimage_mem_nhds hTargetSource'

/-- Helper for Problem 8-29: on the preferred source chart at `1`, the inverse of the
chart-inverse derivative is the ordinary derivative of the chart itself. -/
theorem sourceChartInverseDerivativeAtOne
    {x : EG} (hx : x ∈ (extChartAt I (1 : G)).target) :
    (mfderiv[Set.range I] (extChartAt I (1 : G)).symm x).inverse =
      mfderiv% (extChartAt I (1 : G)) ((extChartAt I (1 : G)).symm x) := by
  -- Normalize the source-side inverse derivative using the preferred-chart inverse identities.
  have hrightInv :
      (extChartAt I (1 : G)) ((extChartAt I (1 : G)).symm x) = x :=
    PartialEquiv.right_inv (extChartAt I (1 : G)) hx
  apply ContinuousLinearMap.inverse_eq
  · simpa [hrightInv] using
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hx
  · simpa [hrightInv] using
      mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hx

/-- Helper for Problem 8-29: on the preferred target chart at `1`, the inverse of the
chart-inverse derivative is the ordinary derivative of the chart itself. -/
theorem targetChartInverseDerivativeAtOne
    {z : H} (hz : z ∈ (extChartAt J (1 : H)).source) :
    (mfderiv[Set.range J] (extChartAt J (1 : H)).symm ((extChartAt J (1 : H)) z)).inverse =
      mfderiv% (extChartAt J (1 : H)) z := by
  -- Normalize the target-side inverse derivative with the same chart identities at `1`.
  apply ContinuousLinearMap.inverse_eq
  · simpa using!
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hz
  · simpa using
      mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hz

/-- Helper for Problem 8-29: once the source and target chart-membership conditions are explicit,
`F`-related vector fields satisfy the preferred-chart pushforward identity pointwise at `1`. -/
theorem chartPushforwardRelatedWithinAtOnePointwise
    (F : ContMDiffMonoidMorphism I J ∞ G H)
    {V : ∀ g : G, TangentSpace I g}
    {W : ∀ h : H, TangentSpace J h}
    (hVW : VectorField.f_related F V W) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let F' := ψ ∘ F ∘ φ.symm
    let V' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm V (Set.range I)
    let W' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm W (Set.range J)
    ∀ ⦃x : EG⦄, x ∈ φ.target →
      F (φ.symm x) ∈ ψ.source →
      fderivWithin 𝕜 F' (Set.range I) x (V' x) = W' (F' x) := by
  let φ := extChartAt I (1 : G)
  let ψ := extChartAt J (1 : H)
  let F' := ψ ∘ F ∘ φ.symm
  let V' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm V (Set.range I)
  let W' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm W (Set.range J)
  dsimp [φ, ψ, F', V', W']
  intro x hx hFx
  change fderivWithin 𝕜 F' (Set.range I) x (V' x) = W' (F' x)
  have hxRange : x ∈ Set.range I :=
    extChartAt_target_subset_range (1 : G) hx
  have hUnique : UniqueMDiffWithinAt 𝓘(𝕜, EG) (Set.range I) x :=
    UniqueDiffWithinAt.uniqueMDiffWithinAt (I.uniqueDiffOn.uniqueDiffWithinAt hxRange)
  have hφdiff :
      MDifferentiableWithinAt 𝓘(𝕜, EG) I φ.symm (Set.range I) x :=
    mdifferentiableWithinAt_extChartAt_symm hx
  have hFContMDiff := hVW.contMDiff
  have hFdiff : MDifferentiableAt I J F (φ.symm x) :=
    hFContMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hψdiff :
      MDifferentiableAt J 𝓘(𝕜, EH) ψ (F (φ.symm x)) := by
    have hChartSource : F (φ.symm x) ∈ (chartAt HH (1 : H)).source := by
      simpa [ψ, extChartAt] using! hFx
    simpa [ψ] using (mdifferentiableAt_extChartAt hChartSource)
  have hψleft : ψ.symm (ψ (F (φ.symm x))) = F (φ.symm x) :=
    PartialEquiv.left_inv ψ hFx
  have hTargetPullback :
      W' (F' x) = mfderiv% ψ (F (φ.symm x)) (W (F (φ.symm x))) := by
    -- Rewrite the target pullback in terms of the preferred target-chart derivative.
    dsimp [W', F']
    rw [VectorField.mpullbackWithin_apply, hψleft]
    exact congrArg (fun L : EH →L[𝕜] EH ↦ L (W (F (φ.symm x))))
      (targetChartInverseDerivativeAtOne hFx)
  have hFcompDiff : MDifferentiableWithinAt 𝓘(𝕜, EG) J (F ∘ φ.symm) (Set.range I) x := by
    simpa [Function.comp] using hFdiff.comp_mdifferentiableWithinAt x hφdiff
  let f : EG → G := φ.symm
  let g : G → H := F
  let h : H → EH := ψ
  -- Route correction: perform the chain-rule normalization in one fixed chart spelling before
  -- applying the pointwise `f_related` identity.
  rw [hTargetPullback]
  dsimp [V']
  rw [VectorField.mpullbackWithin_apply]
  rw [← mfderivWithin_eq_fderivWithin]
  have hψcomp :
      mfderivWithin 𝓘(𝕜, EG) 𝓘(𝕜, EH) (h ∘ (g ∘ f)) (Set.range I) x =
        (mfderiv J 𝓘(𝕜, EH) h (g (f x))).comp
          (mfderivWithin 𝓘(𝕜, EG) J (g ∘ f) (Set.range I) x) := by
    exact (hψdiff.hasMFDerivAt.comp_hasMFDerivWithinAt x hFcompDiff.hasMFDerivWithinAt)
      |>.mfderivWithin hUnique
  have hFcomp :
      mfderivWithin 𝓘(𝕜, EG) J (g ∘ f) (Set.range I) x =
        (mfderiv I J g (f x)).comp
          (mfderivWithin 𝓘(𝕜, EG) I f (Set.range I) x) := by
    exact (hFdiff.hasMFDerivAt.comp_hasMFDerivWithinAt x hφdiff.hasMFDerivWithinAt)
      |>.mfderivWithin hUnique
  rw [show mfderivWithin 𝓘(𝕜, EG) 𝓘(𝕜, EH) (ψ ∘ (F ∘ φ.symm)) (Set.range I) x =
      mfderivWithin 𝓘(𝕜, EG) 𝓘(𝕜, EH) (h ∘ (g ∘ f)) (Set.range I) x by
        rfl]
  rw [hψcomp]
  rw [show mfderivWithin 𝓘(𝕜, EG) J (F ∘ φ.symm) (Set.range I) x =
      mfderivWithin 𝓘(𝕜, EG) J (g ∘ f) (Set.range I) x by
        rfl]
  rw [hFcomp]
  dsimp [f, g, h]
  change
    mfderiv% ψ (F (φ.symm x))
      (mfderiv I J F (φ.symm x)
        ((mfderiv[Set.range I] φ.symm x)
          ((mfderiv[Set.range I] φ.symm x).inverse (V (φ.symm x))))) =
      mfderiv% ψ (F (φ.symm x)) (W (F (φ.symm x)))
  rw [(isInvertible_mfderivWithin_extChartAt_symm hx).self_apply_inverse]
  rw [VectorField.f_related_apply hVW (φ.symm x)]

/-- Helper for Problem 8-29: an `F`-related pair of vector fields becomes an ordinary chart-space
pushforward identity near the preferred chart of `1`. -/
theorem chartPushforwardRelatedWithinAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H)
    {V : ∀ g : G, TangentSpace I g}
    {W : ∀ h : H, TangentSpace J h}
    (hVW : VectorField.f_related F V W) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let F' := ψ ∘ F ∘ φ.symm
    let V' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm V (Set.range I)
    let W' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm W (Set.range J)
    (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (V' x))
      =ᶠ[nhdsWithin (φ (1 : G)) (Set.range I)] fun x ↦ W' (F' x) := by
  dsimp
  -- Wrap the pointwise chart identity into an eventual equality near the preferred chart of `1`.
  filter_upwards [self_mem_nhdsWithin,
    extChartAt_target_mem_nhdsWithin (1 : G),
    chartMapEventuallyIntoTargetSourceAtOne F]
    with x hxRange hxTarget hxSource
  exact chartPushforwardRelatedWithinAtOnePointwise F hVW hxTarget hxSource

/-- Helper for Problem 8-29: an eventual chart-space pushforward identity turns the derivative
term from `VectorField.fderivWithin_apply_lieBracket` into the derivative of the target chart
pullback composed with the chart map of `F`. -/
theorem chartPushforwardDerivativeTermAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H)
    {U Z : EG → EG} {U'' : EH → EH}
    (hU :
      let φ := extChartAt I (1 : G)
      let ψ := extChartAt J (1 : H)
      let F' := ψ ∘ F ∘ φ.symm
      let x0 := φ (1 : G)
      (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (U x))
        =ᶠ[nhdsWithin x0 (Set.range I)] fun x ↦ U'' (F' x))
    (hU'' :
      DifferentiableWithinAt 𝕜 U'' (Set.range J)
        ((extChartAt J (1 : H)) (1 : H))) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let F' := ψ ∘ F ∘ φ.symm
    let x0 := φ (1 : G)
    fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (U x))
      (Set.range I) x0 (Z x0) =
      fderivWithin 𝕜 U'' (Set.range J) (F' x0)
        (fderivWithin 𝕜 F' (Set.range I) x0 (Z x0)) := by
  dsimp at hU ⊢
  have hx0 : ((extChartAt I (1 : G)) (1 : G)) ∈ Set.range I :=
    Set.mem_range_self _
  have hChart :
      ContDiffWithinAt 𝕜 ∞
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (extChartAt I (1 : G)).target ((extChartAt I (1 : G)) (1 : G)) := by
    simpa using inducedLieAlgebraChartMapContDiffWithinAtOne F
  have hUnique : UniqueDiffWithinAt 𝕜 (Set.range I) ((extChartAt I (1 : G)) (1 : G)) :=
    I.uniqueDiffOn.uniqueDiffWithinAt hx0
  have hChartRange :
      ContDiffWithinAt 𝕜 ∞
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (Set.range I) ((extChartAt I (1 : G)) (1 : G)) := by
    -- Restrict the chart-level smoothness of `F` from the chart target to `range I`.
    exact hChart.mono_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin (1 : G))
  have hFdiff :
      DifferentiableWithinAt 𝕜
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (Set.range I) ((extChartAt I (1 : G)) (1 : G)) :=
    hChartRange.differentiableWithinAt (by simp)
  have hMapsTo :
      Set.MapsTo
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (Set.range I) (Set.range J) := by
    -- The preferred target chart always lands in `range J`.
    exact fun x hx ↦ Set.mem_range_self _
  have hU''At :
      DifferentiableWithinAt 𝕜 U'' (Set.range J)
        (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
          ((extChartAt I (1 : G)) (1 : G))) := by
    simpa [Function.comp, F.map_one] using hU''
  -- Rewrite the derivative target by eventual equality, then apply the within-set chain rule.
  rw [Filter.EventuallyEq.fderivWithin_eq_of_mem hU hx0]
  symm
  simpa [Function.comp] using!
    (fderivWithin_fderivWithin hU''At hFdiff hMapsTo hUnique rfl _)

/-- Helper for Problem 8-29: the preferred chart map of `F` sends the source identity chart point
to the target identity chart point. -/
theorem chartMapAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let F' := ψ ∘ F ∘ φ.symm
    F' (φ (1 : G)) = ψ (1 : H) := by
  dsimp
  simp [Function.comp, F.map_one]

/-- Helper for Problem 8-29: the preferred chart map of `F` is `C^∞` within `Set.range I` at the
source identity chart point. -/
theorem preferredChartMapContDiffTopWithinAtOneRange
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let F' := ψ ∘ F ∘ φ.symm
    let x0 := φ (1 : G)
    ContDiffWithinAt 𝕜 ∞ F' (Set.range I) x0 := by
  set φ := extChartAt I (1 : G)
  set ψ := extChartAt J (1 : H)
  set F' : EG → EH := ψ ∘ F ∘ φ.symm
  set x0 : EG := φ (1 : G)
  have hChart :
      ContDiffWithinAt 𝕜 ∞ F' φ.target x0 := by
    -- Reuse the existing preferred-chart smoothness theorem before changing the domain set.
    simpa [φ, ψ, F', x0] using inducedLieAlgebraChartMapContDiffWithinAtOne F
  -- Restrict the preferred-chart smoothness theorem from the chart target to `Set.range I`.
  exact hChart.mono_of_mem_nhdsWithin <| by
    simpa [φ, x0] using extChartAt_target_mem_nhdsWithin (1 : G)

/-- Helper for Problem 8-29: the preferred chart map of `F` has symmetric second derivative on
`Set.range I` at the chart point of `1`. -/
theorem preferredChartMapIsSymmSndFDerivWithinAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let F' := ψ ∘ F ∘ φ.symm
    let x0 := φ (1 : G)
    IsSymmSndFDerivWithinAt 𝕜 F' (Set.range I) x0 := by
  set φ := extChartAt I (1 : G)
  set ψ := extChartAt J (1 : H)
  set F' : EG → EH := ψ ∘ F ∘ φ.symm
  set x0 : EG := φ (1 : G)
  have hx0Range : x0 ∈ Set.range I := by
    exact extChartAt_target_subset_range (1 : G) <| by
      simpa [φ, x0] using mem_extChartAt_target (1 : G)
  have hx0Closure : x0 ∈ closure (interior (Set.range I)) :=
    I.range_subset_closure_interior hx0Range
  have hChartRange :
      ContDiffWithinAt 𝕜 ∞ F' (Set.range I) x0 := by
    -- Reuse the range-level preferred-chart smoothness interface directly.
    simpa [φ, ψ, F', x0] using preferredChartMapContDiffTopWithinAtOneRange F
  have hmin : minSmoothness 𝕜 2 ≤ (∞ : ℕ∞ω) := by
    have htwo_le_inf : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      decide
    simpa [minSmoothness] using htwo_le_inf
  -- Over `IsRCLike` fields, the standard `minSmoothness` theorem gives the required symmetry.
  exact hChartRange.isSymmSndFDerivWithinAt hmin I.uniqueDiffOn hx0Closure hx0Range

/-- Helper for Problem 8-29: at the preferred charts of `1`, the chart map of `F` sends the
source Euclidean Lie bracket to the target Euclidean Lie bracket of the pushed-forward invariant
fields. -/
theorem inducedLieAlgebraBracketChartPushforwardAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let F' := ψ ∘ F ∘ φ.symm
    let X' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm Xᴸ (Set.range I)
    let Y' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm Yᴸ (Set.range I)
    let X'' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm
      ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J)
    let Y'' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm
      ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J)
    fderivWithin 𝕜 F' (Set.range I) (φ (1 : G))
      (VectorField.lieBracketWithin 𝕜 X' Y' (Set.range I) (φ (1 : G))) =
      VectorField.lieBracketWithin 𝕜 X'' Y'' (Set.range J) (ψ (1 : H)) := by
  let φ := extChartAt I (1 : G)
  let ψ := extChartAt J (1 : H)
  let F' : EG → EH := ψ ∘ F ∘ φ.symm
  let X' : EG → EG := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm Xᴸ (Set.range I)
  let Y' : EG → EG := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm Yᴸ (Set.range I)
  let X'' : EH → EH := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm
    ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J)
  let Y'' : EH → EH := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm
    ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J)
  let x0 : EG := φ (1 : G)
  let y0 : EH := ψ (1 : H)
  have hx0Range : x0 ∈ Set.range I := by
    exact extChartAt_target_subset_range (1 : G) <| by
      simpa [φ, x0] using mem_extChartAt_target (1 : G)
  have hx0Closure : x0 ∈ closure (interior (Set.range I)) :=
    I.range_subset_closure_interior hx0Range
  have hChartRange : ContDiffWithinAt 𝕜 ∞ F' (Set.range I) x0 := by
    -- Reuse the range-level preferred-chart smoothness theorem.
    simpa [φ, ψ, F', x0] using preferredChartMapContDiffTopWithinAtOneRange F
  have hmin : minSmoothness 𝕜 2 ≤ (∞ : ℕ∞ω) := by
    have htwo_le_inf : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      decide
    simpa [minSmoothness] using htwo_le_inf
  have hX'Diff : DifferentiableWithinAt 𝕜 X' (Set.range I) x0 := by
    simpa [φ, X', x0] using sourceMulInvariantChartPullbackDifferentiableWithinAtOne X
  have hY'Diff : DifferentiableWithinAt 𝕜 Y' (Set.range I) x0 := by
    simpa [φ, Y', x0] using sourceMulInvariantChartPullbackDifferentiableWithinAtOne Y
  have hX''Diff : DifferentiableWithinAt 𝕜 X'' (Set.range J) y0 := by
    simpa [ψ, X'', y0] using
      targetMulInvariantChartPullbackDifferentiableWithinAtOne
        (inducedLieAlgebraLinearMap F X)
  have hY''Diff : DifferentiableWithinAt 𝕜 Y'' (Set.range J) y0 := by
    simpa [ψ, Y'', y0] using
      targetMulInvariantChartPullbackDifferentiableWithinAtOne
        (inducedLieAlgebraLinearMap F Y)
  have hXpush :
      (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (X' x))
        =ᶠ[nhdsWithin x0 (Set.range I)] fun x ↦ X'' (F' x) := by
    simpa [φ, ψ, F', X', X'', x0] using
      chartPushforwardRelatedWithinAtOne F (inducedLieAlgebraLinearMap_related F X)
  have hYpush :
      (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (Y' x))
        =ᶠ[nhdsWithin x0 (Set.range I)] fun x ↦ Y'' (F' x) := by
    simpa [φ, ψ, F', Y', Y'', x0] using
      chartPushforwardRelatedWithinAtOne F (inducedLieAlgebraLinearMap_related F Y)
  have hXat :
      fderivWithin 𝕜 F' (Set.range I) x0 (X' x0) = X'' (F' x0) :=
    Filter.EventuallyEq.eq_of_nhdsWithin hXpush hx0Range
  have hYat :
      fderivWithin 𝕜 F' (Set.range I) x0 (Y' x0) = Y'' (F' x0) :=
    Filter.EventuallyEq.eq_of_nhdsWithin hYpush hx0Range
  have hFAtOne : F' x0 = y0 := by
    simpa [φ, ψ, F', x0, y0] using chartMapAtOne F
  have hBracket :
      fderivWithin 𝕜 F' (Set.range I) x0
          (VectorField.lieBracketWithin 𝕜 X' Y' (Set.range I) x0) =
        fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (Y' x))
            (Set.range I) x0 (X' x0) -
          fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (X' x))
            (Set.range I) x0 (Y' x0) := by
    -- Apply the vector-space Lie-bracket formula to the preferred chart map of `F`.
    exact VectorField.fderivWithin_apply_lieBracket
      hChartRange hmin I.uniqueDiffOn hx0Closure hx0Range hY'Diff hX'Diff
  have hYterm :
      fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (Y' x))
          (Set.range I) x0 (X' x0) =
        fderivWithin 𝕜 Y'' (Set.range J) (F' x0)
          (fderivWithin 𝕜 F' (Set.range I) x0 (X' x0)) := by
    -- Replace the first derivative term by the derivative of the pushed-forward target field.
    simpa [φ, ψ, F', Y'', x0] using
      chartPushforwardDerivativeTermAtOne F hYpush hY''Diff
  have hXterm :
      fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (X' x))
          (Set.range I) x0 (Y' x0) =
        fderivWithin 𝕜 X'' (Set.range J) (F' x0)
          (fderivWithin 𝕜 F' (Set.range I) x0 (Y' x0)) := by
    -- The second derivative term is normalized in the same way.
    simpa [φ, ψ, F', X'', x0] using
      chartPushforwardDerivativeTermAtOne F hXpush hX''Diff
  have hFinal :
      fderivWithin 𝕜 F' (Set.range I) x0
          (VectorField.lieBracketWithin 𝕜 X' Y' (Set.range I) x0) =
        VectorField.lieBracketWithin 𝕜 X'' Y'' (Set.range J) y0 := by
    -- After normalizing the derivative terms, the target side is exactly the Euclidean bracket.
    calc
      fderivWithin 𝕜 F' (Set.range I) x0
          (VectorField.lieBracketWithin 𝕜 X' Y' (Set.range I) x0)
          =
          fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (Y' x))
              (Set.range I) x0 (X' x0) -
            fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (X' x))
              (Set.range I) x0 (Y' x0) := hBracket
      _ =
          fderivWithin 𝕜 Y'' (Set.range J) (F' x0)
              (fderivWithin 𝕜 F' (Set.range I) x0 (X' x0)) -
            fderivWithin 𝕜 X'' (Set.range J) (F' x0)
              (fderivWithin 𝕜 F' (Set.range I) x0 (Y' x0)) := by
            rw [hYterm, hXterm]
      _ = VectorField.lieBracketWithin 𝕜 X'' Y'' (Set.range J) y0 := by
            simpa [VectorField.lieBracketWithin, hFAtOne, hXat, hYat]
  simpa [φ, ψ, F', X', Y', X'', Y'', x0, y0] using hFinal

/-- Helper for Problem 8-29: differentiating `F` at `1` and then passing to the preferred target
chart agrees with differentiating the preferred-chart expression of `F`. -/
theorem chartDerivativeAtOne_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (v : EG) :
    mfderiv I J F (1 : G) ((mfderiv% (extChartAt I (1 : G)) (1 : G)).inverse v) =
      (mfderiv% (extChartAt J (1 : H)) (1 : H)).inverse
        (fderivWithin 𝕜 ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
          (Set.range I) ((extChartAt I (1 : G)) (1 : G)) v) := by
  let φ := extChartAt I (1 : G)
  let ψ := extChartAt J (1 : H)
  let x0 : EG := φ (1 : G)
  have hx0Symm : φ.symm x0 = (1 : G) := by
    simpa [φ, x0] using PartialEquiv.left_inv φ (mem_extChartAt_source (1 : G))
  have hx0Range : x0 ∈ Set.range I := Set.mem_range_self _
  have hx0Target : x0 ∈ φ.target := by
    simpa [φ, x0] using mem_extChartAt_target (1 : G)
  have hUnique : UniqueMDiffWithinAt 𝓘(𝕜, EG) (Set.range I) x0 :=
    UniqueDiffWithinAt.uniqueMDiffWithinAt (I.uniqueDiffOn.uniqueDiffWithinAt hx0Range)
  have hφdiff :
      MDifferentiableWithinAt 𝓘(𝕜, EG) I φ.symm (Set.range I) x0 := by
    simpa [φ, x0] using mdifferentiableWithinAt_extChartAt_symm hx0Target
  have hFdiff : MDifferentiableAt I J F (1 : G) :=
    F.contMDiff_toFun.mdifferentiableAt (by simp)
  have hFdiff' : MDifferentiableAt I J F (φ.symm x0) := by
    simpa [hx0Symm] using hFdiff
  have hFφdiff :
      MDifferentiableWithinAt 𝓘(𝕜, EG) J (F ∘ φ.symm) (Set.range I) x0 := by
    simpa [Function.comp] using hFdiff'.comp_mdifferentiableWithinAt x0 hφdiff
  have hψdiff : MDifferentiableAt J 𝓘(𝕜, EH) ψ (1 : H) := by
    have hChartSource : (1 : H) ∈ (chartAt HH (1 : H)).source := ChartedSpace.mem_chart_source _
    simpa [ψ] using mdifferentiableAt_extChartAt hChartSource
  have hSourceInverseWithin :
      (mfderiv[Set.range I] φ.symm x0).inverse = mfderiv% φ (1 : G) := by
    have hTmp :
        (mfderiv[Set.range I] φ.symm x0).inverse = mfderiv% φ (φ.symm x0) :=
      sourceChartInverseDerivativeAtOne hx0Target
    have hPoint :
        mfderiv% φ (φ.symm x0) = mfderiv% φ (1 : G) := by
      simpa using
        (show mfderiv I 𝓘(𝕜, EG) φ (φ.symm x0) = mfderiv I 𝓘(𝕜, EG) φ (1 : G) from
          mfderiv_congr_point hx0Symm)
    exact hTmp.trans hPoint
  have hSourceInverse :
      (mfderiv% φ (1 : G)).inverse = mfderiv[Set.range I] φ.symm x0 := by
    have hInvWithin :
        (mfderiv[Set.range I] φ.symm x0).IsInvertible :=
      isInvertible_mfderivWithin_extChartAt_symm hx0Target
    -- Invert the previous identity so the source chart derivative is in the spelling needed below.
    apply ContinuousLinearMap.inverse_eq
    · rw [← hSourceInverseWithin]
      exact hInvWithin.inverse_comp_self
    · rw [← hSourceInverseWithin]
      exact hInvWithin.self_comp_inverse
  -- Route correction: keep the chain rule entirely in the preferred-chart spelling `ψ ∘ F ∘ φ.symm`
  -- and only collapse the chart inverses at the end.
  symm
  have hψinv : (mfderiv J 𝓘(𝕜, EH) ψ (1 : H)).IsInvertible := by
    simpa [ψ] using
      (show (mfderiv J 𝓘(𝕜, EH) (extChartAt J (1 : H)) (1 : H)).IsInvertible from
        isInvertible_mfderiv_extChartAt (mem_extChartAt_source (1 : H)))
  apply (ContinuousLinearMap.IsInvertible.inverse_apply_eq hψinv).2
  rw [← mfderivWithin_eq_fderivWithin]
  -- First peel off the target chart derivative.
  rw [show ψ ∘ F ∘ φ.symm = ψ ∘ (F ∘ φ.symm) by rfl]
  rw [mfderiv_comp_mfderivWithin_of_eq hψdiff hFφdiff hUnique]
  ·
    rw [mfderiv_comp_mfderivWithin_of_eq hFdiff hφdiff hUnique]
    · rw [← hSourceInverse]
      rfl
    · simpa [hx0Symm]
  -- Then peel off the source chart inverse derivative.
  · simpa [Function.comp, hx0Symm, F.map_one]

/-- Helper for Problem 8-29: over an `IsRCLike` field, the derivative at `1` sends the source
manifold bracket of invariant fields to the target manifold bracket of the pushed-forward
invariant fields. -/
theorem inducedLieAlgebraLinearMap_mlieBracket_apply_one_of_isRCLike
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G) :
    mfderiv I J F (1 : G) (VectorField.mlieBracket I Xᴸ Yᴸ (1 : G)) =
      VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
        ((inducedLieAlgebraLinearMap F Y)ᴸ) (1 : H) := by
  let φ := extChartAt I (1 : G)
  let ψ := extChartAt J (1 : H)
  let F' : EG → EH := ψ ∘ F ∘ φ.symm
  let X' : EG → EG := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm Xᴸ (Set.range I)
  let Y' : EG → EG := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm Yᴸ (Set.range I)
  let X'' : EH → EH := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm
    ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J)
  let Y'' : EH → EH := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm
    ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J)
  let x0 : EG := φ (1 : G)
  let y0 : EH := ψ (1 : H)
  let B : EG := VectorField.lieBracketWithin 𝕜 X' Y' (Set.range I) x0
  let C : EH := VectorField.lieBracketWithin 𝕜 X'' Y'' (Set.range J) y0
  have hSourceBracket :
      VectorField.mlieBracket I Xᴸ Yᴸ (1 : G) =
        (mfderiv% φ (1 : G)).inverse B := by
    -- Rewrite the source manifold bracket into the preferred source chart at the identity.
    simpa [φ, X', Y', x0, B, Set.preimage_univ] using
      (VectorField.mlieBracketWithin_apply :
        VectorField.mlieBracketWithin I Xᴸ Yᴸ Set.univ (1 : G) = _)
  have hTargetBracket :
      (mfderiv% ψ (1 : H)).inverse C =
        VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (1 : H) := by
    -- Identify the target chart bracket with the manifold bracket at the identity of `H`.
    simpa [ψ, X'', Y'', y0, C, Set.preimage_univ] using
      (VectorField.mlieBracketWithin_apply :
        VectorField.mlieBracketWithin J ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ) Set.univ (1 : H) = _).symm
  have hChartBracket :
      fderivWithin 𝕜 F' (Set.range I) x0 B = C := by
    -- Reuse the chart-level bracket transport in the exact local chart spelling.
    simpa [φ, ψ, F', X', Y', X'', Y'', x0, y0, B, C] using
      inducedLieAlgebraBracketChartPushforwardAtOne F X Y
  -- Route correction: the chart-level bracket transport is already isolated, so the final proof
  -- only rewrites both manifold brackets into that interface and applies the chart theorem once.
  calc
    mfderiv I J F (1 : G) (VectorField.mlieBracket I Xᴸ Yᴸ (1 : G))
        =
          mfderiv I J F (1 : G) ((mfderiv% φ (1 : G)).inverse B) := by
          rw [hSourceBracket]
    _ =
        (mfderiv% ψ (1 : H)).inverse
          (fderivWithin 𝕜 F' (Set.range I) x0 B) := by
          simpa [φ, ψ, F', x0] using
            (chartDerivativeAtOne_apply F B)
    _ = (mfderiv% ψ (1 : H)).inverse C := by
          rw [hChartBracket]
    _ =
        VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (1 : H) := hTargetBracket

end BracketAtOneChartHelpers

theorem inducedLieAlgebraLinearMap_mlieBracket_apply_one
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G) :
    mfderiv I J F (1 : G) (VectorField.mlieBracket I Xᴸ Yᴸ (1 : G)) =
      VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
        ((inducedLieAlgebraLinearMap F Y)ᴸ) (1 : H) := by
  -- Route correction: the `IsRCLike` chart proof is now local, so the public theorem is just the
  -- stable wrapper around that preferred-chart argument.
  exact inducedLieAlgebraLinearMap_mlieBracket_apply_one_of_isRCLike F X Y

/-- Helper for Problem 8-29: the derivative-at-identity map preserves brackets because invariant
vector fields and the manifold Lie bracket are natural under `f_related`. -/
theorem inducedLieAlgebraLinearMap_map_lie
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G) :
    inducedLieAlgebraLinearMap F ⁅X, Y⁆ =
      ⁅inducedLieAlgebraLinearMap F X, inducedLieAlgebraLinearMap F Y⁆ := by
  have hBracketRelated :
      VectorField.f_related F
        (VectorField.mlieBracket I Xᴸ Yᴸ)
        (VectorField.mlieBracket J
          ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ)) := by
    -- Route correction: consume the stabilized identity-point bracket theorem instead of
    -- rebuilding the chart-level transport inside the final Lie-hom proof.
    exact inducedLieAlgebraLinearMap_mlieBracket_related_of_applyOne F X Y <|
      inducedLieAlgebraLinearMap_mlieBracket_apply_one F X Y
  -- Once the bracket fields are known to be `F`-related, evaluating at `1` recovers the
  -- Lie-algebra bracket identity.
  exact inducedLieAlgebraLinearMap_map_lie_of_related F X Y hBracketRelated

/-- Helper for Problem 8-29: the derivative-at-identity map of a smooth monoid homomorphism,
packaged as a Lie algebra homomorphism. -/
noncomputable def inducedLieAlgebraHomomorphism
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    GroupLieAlgebra I G →ₗ⁅𝕜⁆ GroupLieAlgebra J H where
  toLinearMap := inducedLieAlgebraLinearMap F
  map_lie' := by
    intro X Y
    exact inducedLieAlgebraLinearMap_map_lie F X Y

scoped notation:max F "_*" => inducedLieAlgebraHomomorphism F
scoped notation:max F "_* " X => inducedLieAlgebraHomomorphism F X
scoped notation:max "(" F ")" "_*" => inducedLieAlgebraHomomorphism F
scoped notation:max "(" F ")" "_* " X => inducedLieAlgebraHomomorphism F X

/-- Helper for Problem 8-29: the induced Lie algebra homomorphism of the identity map is the
identity on the group Lie algebra. -/
@[simp] theorem id_inducedLieAlgebraHomomorphism
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {I : ModelWithCorners 𝕜 EG HG}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    [LieGroup I ∞ G] :
    ((ContMDiffMonoidMorphism.id : ContMDiffMonoidMorphism I I ∞ G G))_* = 1 := by
  apply LieHom.ext
  intro X
  change inducedLieAlgebraLinearMap
    (ContMDiffMonoidMorphism.id : ContMDiffMonoidMorphism I I ∞ G G) X = X
  rw [inducedLieAlgebraLinearMap_apply]
  have h := mfderiv_id (I := I) (x := (1 : G))
  simpa only [ContinuousLinearMap.id_apply] using!
    congrArg (fun L : EG →L[𝕜] EG ↦ L X) h

/-- Helper for Problem 8-29: induced Lie algebra homomorphisms are functorial under composition. -/
@[simp] theorem inducedLieAlgebraHomomorphism_comp
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK] [CompleteSpace EK]
    {HK : Type*} [TopologicalSpace HK]
    {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
    {K : ModelWithCorners 𝕜 EK HK}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    {K' : Type*} [TopologicalSpace K'] [ChartedSpace HK K'] [Group K']
    [LieGroup I ∞ G] [LieGroup J ∞ H] [LieGroup K ∞ K']
    (F₂ : ContMDiffMonoidMorphism J K ∞ H K')
    (F₁ : ContMDiffMonoidMorphism I J ∞ G H) :
    (F₂.comp F₁)_* = ((F₂)_*).comp ((F₁)_*) := by
  ext X
  have hF₁ : MDifferentiableAt I J F₁ (1 : G) :=
    F₁.contMDiff_toFun.mdifferentiableAt (by simp)
  have hF₂ : MDifferentiableAt J K F₂ (1 : H) :=
    F₂.contMDiff_toFun.mdifferentiableAt (by simp)
  -- Evaluate both induced maps at `X` and invoke the chain rule at the identity.
  simpa [LieHom.comp_apply, inducedLieAlgebraLinearMap_apply] using!
    (mfderiv_comp_apply_of_eq (1 : G) hF₂ hF₁ F₁.map_one X)

end ContMDiffMonoidMorphism

section CanonicalLieSubalgebra

universe u𝕜 uE uH uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I (⊤ : WithTop ℕ∞) G]

namespace LieSubgroup

/-- Helper for Problem 8-29: a Lie subgroup of a finite-dimensional ambient Lie group has a
finite-dimensional model space. -/
theorem finiteDimensionalModelSpace
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [FiniteDimensional 𝕜 E] :
    FiniteDimensional 𝕜 S.ModelSpace := by
  let x : S.carrier := 1
  let hImm := S.subtype_val_isImmersion.isImmersionAt x
  let _ : FiniteDimensional 𝕜 (S.ModelSpace × hImm.complement) :=
    FiniteDimensional.of_injective hImm.equiv.toLinearMap hImm.equiv.injective
  exact
    FiniteDimensional.of_injective
      (ContinuousLinearMap.inl 𝕜 S.ModelSpace hImm.complement).toLinearMap
      LinearMap.inl_injective

local instance
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [FiniteDimensional 𝕜 E] :
    FiniteDimensional 𝕜 S.ModelSpace :=
  finiteDimensionalModelSpace S

local instance (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) :
    LieGroup (modelWithCornersSelf 𝕜 S.ModelSpace) (minSmoothness 𝕜 3) S.carrier :=
  LieGroup.of_le <| show minSmoothness 𝕜 3 ≤ (⊤ : WithTop ℕ∞) by
    exact le_top

local instance : LieGroup I (minSmoothness 𝕜 3) G :=
  LieGroup.of_le <| show minSmoothness 𝕜 3 ≤ (⊤ : WithTop ℕ∞) by
    exact le_top

/-- Helper for Problem 8-29: lowering the subgroup inclusion immersion from `⊤` to `∞` keeps the
same local normal form. -/
theorem subtypeVal_isImmersionAtInfinity
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) :
    Manifold.IsImmersion (modelWithCornersSelf 𝕜 S.ModelSpace) I ∞
      (Subtype.val : S.carrier → G) := by
  let hComp := S.subtype_val_isImmersion.complement
  let hCompImm := S.subtype_val_isImmersion.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact IsManifold.maximalAtlas_subset_of_le (by simp) hx.domChart_mem_maximalAtlas
  · exact IsManifold.maximalAtlas_subset_of_le (by simp) hx.codChart_mem_maximalAtlas

/-- Helper for Problem 8-29: the subgroup inclusion is smooth at the `C^∞` level expected by the
group-Lie-algebra owner. -/
theorem contMDiff_subtype_val
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace] :
    ContMDiff (modelWithCornersSelf 𝕜 S.ModelSpace) I ∞ (Subtype.val : S.carrier → G) := by
  exact (subtypeVal_isImmersionAtInfinity S).contMDiff

/-- Helper for Problem 8-29: the derivative of a maximal-atlas chart extension is injective at
points in its source because it has a derivative-level left inverse. -/
private theorem chartExtend_symm_mdifferentiableWithin_range
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    {e : OpenPartialHomeomorph N H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ N) {p : N} (hp : p ∈ e.source) :
    MDifferentiableWithinAt (modelWithCornersSelf 𝕜 E) I (e.extend I).symm (Set.range I)
      (e.extend I p) := by
  letI : IsManifold I 1 N :=
    IsManifold.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have he_one : e ∈ IsManifold.maximalAtlas I 1 N :=
    IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞) he
  have hid :
      MDifferentiableWithinAt I I (id : N → N) Set.univ p := by
    -- The inverse-chart derivative bridge starts from the trivial differentiability of `id`.
    simpa using
      (mdifferentiableWithinAt_id :
        MDifferentiableWithinAt I I (id : N → N) Set.univ p)
  -- Re-express `id` in chart coordinates to read off differentiability of the inverse chart.
  simpa [Function.comp] using
    (mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas he_one hp).mp hid

/-- Helper for Problem 8-29: differentiating the chart left-inverse identity on `e.source`
produces a concrete left inverse for the derivative of `e.extend`. -/
private theorem chartExtend_mfderiv_left_inverse
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    {e : OpenPartialHomeomorph N H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ N) {p : N} (hp : p ∈ e.source) :
    (mfderivWithin (modelWithCornersSelf 𝕜 E) I (e.extend I).symm (Set.range I) (e.extend I p)).comp
      (mfderiv I (modelWithCornersSelf 𝕜 E) (e.extend I) p) =
        ContinuousLinearMap.id 𝕜 (TangentSpace I p) := by
  letI : IsManifold I 1 N :=
    IsManifold.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have he_one : e ∈ IsManifold.maximalAtlas I 1 N :=
    IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞) he
  have hsource_unique : UniqueMDiffWithinAt I e.source p :=
    e.open_source.uniqueMDiffWithinAt hp
  have hchart :
      MDifferentiableAt I (modelWithCornersSelf 𝕜 E) (e.extend I) p := by
    -- Maximal-atlas charts are differentiable at every source point.
    exact
      (OpenPartialHomeomorph.contMDiffAt_extend he_one hp).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hrange :
      MDifferentiableWithinAt (modelWithCornersSelf 𝕜 E) I (e.extend I).symm (Set.range I)
        (e.extend I p) :=
    chartExtend_symm_mdifferentiableWithin_range he hp
  have hchart_within :
      mfderiv I (modelWithCornersSelf 𝕜 E) (e.extend I) p =
        mfderivWithin I (modelWithCornersSelf 𝕜 E) (e.extend I) e.source p := by
    -- On the open chart source, the within derivative agrees with the ordinary derivative.
    symm
    exact mfderivWithin_eq_mfderiv hsource_unique hchart
  rw [hchart_within, ← mfderivWithin_comp_of_eq]
  · -- Differentiate the left-inverse identity on the chart source where the source-side
    -- `UniqueMDiffWithinAt` hypothesis is available.
    rw [← mfderivWithin_id hsource_unique]
    apply Filter.EventuallyEq.mfderivWithin_eq_of_mem
    · refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
      intro z hz
      simpa [Function.comp] using
        (show (e.extend I).symm (e.extend I z) = z from e.extend_left_inv hz)
    · exact hp
  · exact hrange
  · exact hchart.mdifferentiableWithinAt
  · intro z hz
    have hz_target : e.extend I z ∈ (e.extend I).target :=
      (e.extend I).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hz
    exact e.extend_target_subset_range hz_target
  · exact hsource_unique
  · rfl

/-- Helper for Problem 8-29: the derivative of a maximal-atlas chart extension is injective at
points in its source because it has a derivative-level left inverse. -/
private theorem chartExtend_mfderiv_injective
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] {e : OpenPartialHomeomorph N H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ N) {p : N} (hp : p ∈ e.source) :
    Function.Injective (mfderiv I (modelWithCornersSelf 𝕜 E) (e.extend I) p) := by
  let Linv :=
    mfderivWithin (modelWithCornersSelf 𝕜 E) I (e.extend I).symm (Set.range I) (e.extend I p)
  intro w₁ w₂ hw
  have hleft := chartExtend_mfderiv_left_inverse he hp
  have hp_left : (e.extend I).symm (e.extend I p) = p :=
    e.extend_left_inv hp
  have hw_push :
      Linv (mfderiv I (modelWithCornersSelf 𝕜 E) (e.extend I) p w₁) =
        Linv (mfderiv I (modelWithCornersSelf 𝕜 E) (e.extend I) p w₂) := by
    simpa [Linv] using congrArg Linv hw
  have hw₁ :
      ((Linv.comp (mfderiv I (modelWithCornersSelf 𝕜 E) (e.extend I) p)) w₁) = w₁ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using!
      congrArg (fun L ↦ L w₁) hleft
  have hw₂ :
      ((Linv.comp (mfderiv I (modelWithCornersSelf 𝕜 E) (e.extend I) p)) w₂) = w₂ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using!
      congrArg (fun L ↦ L w₂) hleft
  have hw₁' : w₁ = Linv (mfderiv I (modelWithCornersSelf 𝕜 E) (e.extend I) p w₁) := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using hw₁.symm
  have hw₂' : Linv (mfderiv I (modelWithCornersSelf 𝕜 E) (e.extend I) p w₂) = w₂ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using hw₂
  -- Apply the derivative-level left inverse to both chart-coordinate tangent vectors.
  exact hw₁'.trans (hw_push.trans hw₂')

/-- Helper for Problem 8-29: differentiating the subgroup immersion normal form identifies the
ambient derivative of `Subtype.val` with the linear model map from the immersion chart. -/
private theorem subtypeVal_chartPushforward_eq_model
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I)
    (hImm : Manifold.IsImmersion (modelWithCornersSelf 𝕜 S.ModelSpace) I ∞
      (Subtype.val : S.carrier → G))
    (p : S.carrier) (w : TangentSpace (modelWithCornersSelf 𝕜 S.ModelSpace) p) :
    let hImmAt := hImm.isImmersionAt p
    let equiv : (S.ModelSpace × hImmAt.complement) →L[𝕜] E := hImmAt.equiv.toContinuousLinearMap
    let L : S.ModelSpace →L[𝕜] E :=
      equiv.comp (ContinuousLinearMap.inl 𝕜 S.ModelSpace hImmAt.complement)
    (mfderiv I (modelWithCornersSelf 𝕜 E) (hImmAt.codChart.extend I) ((Subtype.val : S.carrier → G) p))
      (mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) I (Subtype.val : S.carrier → G) p w) =
        L ((mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) (modelWithCornersSelf 𝕜 S.ModelSpace)
          (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) p) w) := by
  let hImmAt := hImm.isImmersionAt p
  let equiv : (S.ModelSpace × hImmAt.complement) →L[𝕜] E := hImmAt.equiv.toContinuousLinearMap
  let L : S.ModelSpace →L[𝕜] E :=
    equiv.comp (ContinuousLinearMap.inl 𝕜 S.ModelSpace hImmAt.complement)
  have hdomChart_source : hImmAt.domChart.source ∈ nhds p :=
    IsOpen.mem_nhds hImmAt.domChart.open_source hImmAt.mem_domChart_source
  have hEqOn :
      Set.EqOn ((hImmAt.codChart.extend I) ∘ (Subtype.val : S.carrier → G))
        (L ∘ (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)))
        hImmAt.domChart.source := by
    intro y hy
    -- Read the immersion normal form directly on the source chart neighborhood.
    have hy_target :
        hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) y ∈
          (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).target :=
      (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hy
    simpa [Function.comp, L, OpenPartialHomeomorph.extend_coe,
      hImmAt.domChart.left_inv hy, ContinuousLinearMap.comp_apply] using!
      hImmAt.writtenInCharts hy_target
  have hEq :
      ((hImmAt.codChart.extend I) ∘ (Subtype.val : S.carrier → G)) =ᶠ[nhds p]
        L ∘ (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) :=
    hEqOn.eventuallyEq_of_mem hdomChart_source
  have hsub :
      MDifferentiableAt (modelWithCornersSelf 𝕜 S.ModelSpace) I (Subtype.val : S.carrier → G) p :=
    hImm.contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hdomChart_mem_maximalAtlas_one :
      hImmAt.domChart ∈ IsManifold.maximalAtlas (modelWithCornersSelf 𝕜 S.ModelSpace) 1 S.carrier :=
    IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
      hImmAt.domChart_mem_maximalAtlas
  have hcodChart_mem_maximalAtlas_one :
      hImmAt.codChart ∈ IsManifold.maximalAtlas I 1 G :=
    IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
      hImmAt.codChart_mem_maximalAtlas
  have hdom :
      MDifferentiableAt (modelWithCornersSelf 𝕜 S.ModelSpace)
        (modelWithCornersSelf 𝕜 S.ModelSpace)
        (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) p := by
    -- Maximal-atlas charts are differentiable in model coordinates.
    exact
      (OpenPartialHomeomorph.contMDiffAt_extend hdomChart_mem_maximalAtlas_one
        hImmAt.mem_domChart_source).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hcod :
      MDifferentiableAt I (modelWithCornersSelf 𝕜 E) (hImmAt.codChart.extend I)
        ((Subtype.val : S.carrier → G) p) := by
    -- The ambient chart enjoys the same differentiability property.
    exact
      (OpenPartialHomeomorph.contMDiffAt_extend hcodChart_mem_maximalAtlas_one
        hImmAt.mem_codChart_source).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hL :
      MDifferentiableAt (modelWithCornersSelf 𝕜 S.ModelSpace) (modelWithCornersSelf 𝕜 E) L
        (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) p) := by
    -- The linear model map differentiates to itself.
    exact L.contMDiffAt.mdifferentiableAt (by simp : (1 : ℕ∞ω) ≠ 0)
  have hLfderiv :
      fderiv 𝕜 (⇑L) (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) p) = L :=
    L.fderiv
  have hmfderiv_eq :
      mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) (modelWithCornersSelf 𝕜 E)
        (((hImmAt.codChart.extend I) ∘ (Subtype.val : S.carrier → G))) p =
          mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) (modelWithCornersSelf 𝕜 E)
            (L ∘ (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace))) p := by
    -- Differentiate the two eventually equal source-side expressions at the base point.
    exact hEq.mfderiv_eq
  have hleft :
      (mfderiv I (modelWithCornersSelf 𝕜 E) (hImmAt.codChart.extend I)
          ((Subtype.val : S.carrier → G) p))
        (mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) I (Subtype.val : S.carrier → G) p w) =
          mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) (modelWithCornersSelf 𝕜 E)
            (((hImmAt.codChart.extend I) ∘ (Subtype.val : S.carrier → G))) p w := by
    rw [mfderiv_comp _ hcod hsub]
    rfl
  have hright :
      mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) (modelWithCornersSelf 𝕜 E)
          (L ∘ (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace))) p w =
        L ((mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) (modelWithCornersSelf 𝕜 S.ModelSpace)
          (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) p) w) := by
    rw [mfderiv_comp _ hL hdom, mfderiv_eq_fderiv, hLfderiv]
    rfl
  -- Apply the chain rule on both sides of the source-side equality.
  exact hleft.trans <| hmfderiv_eq ▸ hright

/-- Helper for Problem 8-29: the derivative of the subgroup inclusion at the identity is
injective because the subgroup inclusion is an immersion in local charts. -/
private theorem subtypeVal_mfderiv_injective_atOne
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace] :
    Function.Injective
      (mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (Subtype.val : S.carrier → G) (1 : S.carrier)) := by
  let hImm : Manifold.IsImmersion (modelWithCornersSelf 𝕜 S.ModelSpace) I ∞
      (Subtype.val : S.carrier → G) :=
    subtypeVal_isImmersionAtInfinity S
  let hImmAt := hImm.isImmersionAt (1 : S.carrier)
  let equiv : (S.ModelSpace × hImmAt.complement) →L[𝕜] E := hImmAt.equiv.toContinuousLinearMap
  let L : S.ModelSpace →L[𝕜] E :=
    equiv.comp (ContinuousLinearMap.inl 𝕜 S.ModelSpace hImmAt.complement)
  have hL_injective : Function.Injective L := by
    intro u v huv
    have hpair :
        (u, (0 : hImmAt.complement)) = (v, (0 : hImmAt.complement)) := by
      apply hImmAt.equiv.injective
      simpa [L, equiv, ContinuousLinearMap.comp_apply] using huv
    exact (Prod.mk.inj hpair).1
  intro w₁ w₂ hw
  have hw_chart :
      L ((mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace)
          (modelWithCornersSelf 𝕜 S.ModelSpace)
          (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) (1 : S.carrier)) w₁) =
        L ((mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace)
          (modelWithCornersSelf 𝕜 S.ModelSpace)
          (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) (1 : S.carrier)) w₂) := by
    have hw₁_model :
        L ((mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace)
            (modelWithCornersSelf 𝕜 S.ModelSpace)
            (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) (1 : S.carrier)) w₁) =
          (mfderiv I (modelWithCornersSelf 𝕜 E) (hImmAt.codChart.extend I)
              ((Subtype.val : S.carrier → G) (1 : S.carrier)))
            (mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) I
              (Subtype.val : S.carrier → G) (1 : S.carrier) w₁) := by
      simpa [hImmAt, L] using!
        (subtypeVal_chartPushforward_eq_model S hImm (1 : S.carrier) w₁).symm
    have hw₂_model :
        (mfderiv I (modelWithCornersSelf 𝕜 E) (hImmAt.codChart.extend I)
            ((Subtype.val : S.carrier → G) (1 : S.carrier)))
          (mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) I
            (Subtype.val : S.carrier → G) (1 : S.carrier) w₂) =
            L ((mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace)
              (modelWithCornersSelf 𝕜 S.ModelSpace)
              (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) (1 : S.carrier)) w₂) := by
      simpa [hImmAt, L] using!
        subtypeVal_chartPushforward_eq_model S hImm (1 : S.carrier) w₂
    -- Compare the two vectors after applying the ambient chart derivative.
    exact hw₁_model.trans <|
      (congrArg
        (mfderiv I (modelWithCornersSelf 𝕜 E) (hImmAt.codChart.extend I)
          ((Subtype.val : S.carrier → G) (1 : S.carrier))) hw).trans hw₂_model
  have hsource_chart :
      (mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace)
          (modelWithCornersSelf 𝕜 S.ModelSpace)
          (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) (1 : S.carrier)) w₁ =
        (mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace)
          (modelWithCornersSelf 𝕜 S.ModelSpace)
          (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) (1 : S.carrier)) w₂ :=
    hL_injective hw_chart
  have hdomChart_injective :
      Function.Injective
        (mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace)
          (modelWithCornersSelf 𝕜 S.ModelSpace)
          (hImmAt.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) (1 : S.carrier)) :=
    chartExtend_mfderiv_injective hImmAt.domChart_mem_maximalAtlas hImmAt.mem_domChart_source
  -- Cancel the source chart derivative using its chart-level left inverse.
  exact hdomChart_injective hsource_chart

/-- Helper for Problem 8-29: the Lie-subgroup inclusion packaged as a smooth monoid
homomorphism. -/
def inclusion
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace] :
    ContMDiffMonoidMorphism (modelWithCornersSelf 𝕜 S.ModelSpace) I ∞ S.carrier G where
  toMonoidHom := S.carrier.subtype
  contMDiff_toFun := contMDiff_subtype_val S

/-- Helper for Problem 8-29: the induced Lie algebra homomorphism of the subgroup inclusion is
injective. -/
theorem inclusion_inducedLieAlgebraHomomorphism_injective
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace]
    [FiniteDimensional 𝕜 E] :
    Function.Injective ((inclusion S)_*) := by
  -- Reduce injectivity to the derivative of `Subtype.val` at the identity and use the direct
  -- chart-level injectivity lemma proved just above.
  have hMfderivInj :
      Function.Injective
        (mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) I
          (Subtype.val : S.carrier → G) (1 : S.carrier)) :=
    subtypeVal_mfderiv_injective_atOne S
  intro X Y hXY
  apply hMfderivInj
  simpa [LieSubgroup.inclusion, ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism,
    ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap,
    ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap_apply] using! hXY

/-- The canonical ambient Lie subalgebra attached to a Lie subgroup. -/
def groupLieSubalgebra
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace] :
    LieSubalgebra 𝕜 (GroupLieAlgebra I G) :=
  LieHom.range ((inclusion S)_*)

/-- The Lie algebra of a Lie subgroup is canonically equivalent to its image in the ambient Lie
algebra. -/
noncomputable def groupLieSubalgebraEquiv
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace]
    [FiniteDimensional 𝕜 E] :
    GroupLieAlgebra (modelWithCornersSelf 𝕜 S.ModelSpace) S.carrier ≃ₗ⁅𝕜⁆
      groupLieSubalgebra S :=
  LieEquiv.ofInjective
    ((inclusion S)_*) (LieSubgroup.inclusion_inducedLieAlgebraHomomorphism_injective S)

/-- Helper for Problem 8-29: the subgroup Lie algebra is definitionally the range of the
inclusion derivative. -/
theorem groupLieSubalgebra_eq_range
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace] :
    groupLieSubalgebra S = LieHom.range ((inclusion S)_*) := rfl

/-- Helper for Problem 8-29: membership in the subgroup Lie algebra means belonging to the image
of the inclusion derivative at the identity. -/
theorem mem_groupLieSubalgebra_iff
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace]
    (X : GroupLieAlgebra I G) :
    X ∈ groupLieSubalgebra S ↔
      ∃ Y : GroupLieAlgebra (modelWithCornersSelf 𝕜 S.ModelSpace) S.carrier,
        ((inclusion S)_*) Y = X := by
  rfl

/-- Helper for Problem 8-29: membership in the subgroup Lie algebra can be read as the existence
of a tangent vector at the identity whose image under the inclusion derivative is the ambient
matrix. -/
theorem mem_groupLieSubalgebra_iff_exists_subgroupTangent
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace]
    (X : GroupLieAlgebra I G) :
    X ∈ groupLieSubalgebra S ↔
      ∃ v : TangentSpace (modelWithCornersSelf 𝕜 S.ModelSpace) (1 : S.carrier),
        mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) I
          (Subtype.val : S.carrier → G) (1 : S.carrier) v = X := by
  -- Unpack the range definition once, then rewrite the induced Lie map as the subgroup inclusion
  -- derivative at the identity.
  rw [mem_groupLieSubalgebra_iff]
  constructor
  · rintro ⟨Y, hY⟩
    refine ⟨Y, ?_⟩
    simpa [LieSubgroup.inclusion, ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism,
      ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap,
      ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap_apply] using! hY
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa [LieSubgroup.inclusion, ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism,
      ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap,
      ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap_apply] using! hv

end LieSubgroup

end CanonicalLieSubalgebra

/- These determinant lemmas are intentionally elaborated before the operator-norm matrix
instances below.  This keeps the standard matrix additive/module structures coherent while the
operator norm is introduced later only for the matrix Lie-group manifolds. -/

private noncomputable def matrixTraceContinuousLinearMap
    {R : Type*} [NontriviallyNormedField R] [CompleteSpace R]
    (n : ℕ) [NormedRing (Matrix (Fin n) (Fin n) R)]
    [NormedAlgebra R (Matrix (Fin n) (Fin n) R)] :
    Matrix (Fin n) (Fin n) R →L[R] R :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin n) R R)

attribute [-instance] LieRing.ofAssociativeRing in
private theorem matrixDet_differentiableAt_one
    {R : Type*} [NontriviallyNormedField R] [CompleteSpace R]
    (n : ℕ) [NormedRing (Matrix (Fin n) (Fin n) R)]
    [NormedAlgebra R (Matrix (Fin n) (Fin n) R)] :
    DifferentiableAt R
      (Matrix.det : Matrix (Fin n) (Fin n) R → R) 1 := by
  let detContinuous : (Fin n → R) [⋀^(Fin n)]→L[R] R :=
    { toContinuousMultilinearMap :=
        { toMultilinearMap :=
            (Matrix.detRowAlternating : (Fin n → R) [⋀^(Fin n)]→ₗ[R] R).toMultilinearMap
          cont := by
            change Continuous
              (fun M : Matrix (Fin n) (Fin n) R ↦ Matrix.det M)
            exact Continuous.matrix_det continuous_id }
      map_eq_zero_of_eq' :=
        (Matrix.detRowAlternating :
          (Fin n → R) [⋀^(Fin n)]→ₗ[R] R).map_eq_zero_of_eq' }
  have h := detContinuous.differentiable (1 : Matrix (Fin n) (Fin n) R)
  simpa [detContinuous] using! h

attribute [-instance] LieRing.ofAssociativeRing in
private theorem matrixDet_polynomialLine
    {R : Type*} [NontriviallyNormedField R]
    (n : ℕ) [NormedRing (Matrix (Fin n) (Fin n) R)]
    [NormedAlgebra R (Matrix (Fin n) (Fin n) R)]
    (X : Matrix (Fin n) (Fin n) R) :
    (fun t : R ↦ Matrix.det (1 + t • X)) =
      fun t ↦ Polynomial.eval t
        (((1 : Matrix (Fin n) (Fin n) (Polynomial R)) +
          (Polynomial.X : Polynomial R) • X.map Polynomial.C).det) := by
  funext t
  change (1 + t • X).det =
    (Polynomial.evalRingHom t)
      (((1 : Matrix (Fin n) (Fin n) (Polynomial R)) +
        (Polynomial.X : Polynomial R) • X.map Polynomial.C).det)
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, map_add, map_mul]
  rw [mul_comm t (X i j)]
  change (1 : Matrix (Fin n) (Fin n) R) i j + X i j * t =
    Polynomial.eval t ((1 : Matrix (Fin n) (Fin n) (Polynomial R)) i j) +
      Polynomial.eval t Polynomial.X * Polynomial.eval t (Polynomial.C (X i j))
  rw [Polynomial.eval_X, Polynomial.eval_C, mul_comm]
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Polynomial.eval_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, Polynomial.eval_zero]

attribute [-instance] LieRing.ofAssociativeRing in
private theorem matrixDet_line_hasDerivAt
    {R : Type*} [NontriviallyNormedField R]
    (n : ℕ) [NormedRing (Matrix (Fin n) (Fin n) R)]
    [NormedAlgebra R (Matrix (Fin n) (Fin n) R)]
    (X : Matrix (Fin n) (Fin n) R) :
    HasDerivAt (fun t : R ↦ Matrix.det (1 + t • X)) (Matrix.trace X) 0 := by
  rw [matrixDet_polynomialLine n X]
  convert
    (Polynomial.hasDerivAt
      (((1 : Matrix (Fin n) (Fin n) (Polynomial R)) +
        (Polynomial.X : Polynomial R) • X.map Polynomial.C).det) 0) using 1
  exact (Matrix.derivative_det_one_add_X_smul X).symm

attribute [-instance] LieRing.ofAssociativeRing in
private theorem matrixDet_fderiv_one_apply
    {R : Type*} [NontriviallyNormedField R] [CompleteSpace R]
    (n : ℕ) [NormedRing (Matrix (Fin n) (Fin n) R)]
    [NormedAlgebra R (Matrix (Fin n) (Fin n) R)]
    (X : Matrix (Fin n) (Fin n) R) :
    fderiv R (Matrix.det : Matrix (Fin n) (Fin n) R → R) 1 X =
      Matrix.trace X := by
  let detContinuous : (Fin n → R) [⋀^(Fin n)]→L[R] R :=
    { toContinuousMultilinearMap :=
        { toMultilinearMap :=
            (Matrix.detRowAlternating : (Fin n → R) [⋀^(Fin n)]→ₗ[R] R).toMultilinearMap
          cont := by
            change Continuous
              (fun M : Matrix (Fin n) (Fin n) R ↦ Matrix.det M)
            exact Continuous.matrix_det continuous_id }
      map_eq_zero_of_eq' :=
        (Matrix.detRowAlternating :
          (Fin n → R) [⋀^(Fin n)]→ₗ[R] R).map_eq_zero_of_eq' }
  let oneM : Fin n → Fin n → R := fun i j => (1 : Matrix (Fin n) (Fin n) R) i j
  have hfun :
      (Matrix.det : Matrix (Fin n) (Fin n) R → R) = fun M => detContinuous M := by
    funext M
    exact (rfl : Matrix.det M = detContinuous M)
  have hF : HasFDerivAt (fun M : Fin n → Fin n → R => detContinuous M)
      (detContinuous.1.linearDeriv oneM) oneM :=
    detContinuous.hasFDerivAt oneM
  have hterm : ∀ i : Fin n,
      detContinuous (Function.update oneM i (X i)) = X i i := by
    intro i
    have hupd :
        Function.update oneM i (X i) =
          Matrix.updateRow (1 : Matrix (Fin n) (Fin n) R) i (X i) := by
      ext a b
      simp [oneM, Matrix.updateRow]
    change Matrix.det (Function.update oneM i (X i)) = X i i
    rw [hupd, ← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
    simp
  have hsum : detContinuous.1.linearDeriv oneM (fun i j => X i j) = Matrix.trace X := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    simpa [oneM] using hterm i
  have hfderiv :
      fderiv R (fun M : Fin n → Fin n → R => detContinuous M) oneM =
        detContinuous.1.linearDeriv oneM :=
    hF.fderiv
  have hgoal :
      fderiv R (Matrix.det : Matrix (Fin n) (Fin n) R → R) 1 X =
        detContinuous.1.linearDeriv oneM (fun i j => X i j) := by
    rw [hfun]
    exact congrArg (fun L : (Fin n → Fin n → R) →L[R] R ↦ L (fun i j => X i j)) hfderiv
  exact hgoal.trans hsum

attribute [-instance] LieRing.ofAssociativeRing in
private theorem matrixDet_hasFDerivAt_one
    {R : Type*} [NontriviallyNormedField R] [CompleteSpace R]
    (n : ℕ) [NormedRing (Matrix (Fin n) (Fin n) R)]
    [NormedAlgebra R (Matrix (Fin n) (Fin n) R)] :
    HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) R → R)
      (matrixTraceContinuousLinearMap n) 1 := by
  have hd := (matrixDet_differentiableAt_one (R := R) n).hasFDerivAt
  apply hd.congr_fderiv
  ext X
  exact matrixDet_fderiv_one_apply (R := R) n X

/-- The operator-normed ring structure on real `n × n` matrices used by the real matrix models. -/
local instance real_matrix_normedRing (n : ℕ) : NormedRing (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.linftyOpNormedRing

/-- The corresponding normed real-algebra structure on real `n × n` matrices. -/
local instance real_matrix_normedAlgebra (n : ℕ) :
    NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.linftyOpNormedAlgebra

local instance real_matrix_completeSpace (n : ℕ) :
    CompleteSpace (Matrix (Fin n) (Fin n) ℝ) := by
  infer_instance

/-- The operator-normed ring structure on complex `n × n` matrices used by the complex matrix
models. -/
local instance complex_matrix_normedRing (n : ℕ) : NormedRing (Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.linftyOpNormedRing

/-- The corresponding normed complex-algebra structure on complex `n × n` matrices. -/
local instance complex_matrix_normedAlgebra (n : ℕ) :
    NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.linftyOpNormedAlgebra

local instance complex_matrix_completeSpace (n : ℕ) :
    CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := by
  infer_instance

local notation "RealLieSubgroupGL(" n ")" =>
  @LieSubgroup ℝ inferInstance (Mℝ(n)) inferInstance inferInstance (Mℝ(n)) inferInstance
    (GL (Fin n) ℝ) inferInstance inferInstance (realGeneralLinearGroupChartedSpace n) (Iℝ(n))

local notation "ComplexLieSubgroupGL(" n ")" =>
  @LieSubgroup ℂ inferInstance (Mℂ(n)) inferInstance inferInstance (Mℂ(n)) inferInstance
    (GL (Fin n) ℂ) inferInstance inferInstance (complexGeneralLinearGroupChartedSpace n) (Iℂ(n))

local notation "RealLieSubgroupGLComplex(" n ")" =>
  @LieSubgroup ℝ inferInstance (Mℂ(n)) inferInstance inferInstance (Mℂ(n)) inferInstance
    (GL (Fin n) ℂ) inferInstance inferInstance (complexGeneralLinearGroupChartedSpace n)
      (Iℝℂ(n))

local instance realGeneralLinearGroupChartedSpaceInst (n : ℕ) :
    ChartedSpace (Mℝ(n)) (GL (Fin n) ℝ) :=
  realGeneralLinearGroupChartedSpace n

local instance complexGeneralLinearGroupChartedSpaceInst (n : ℕ) :
    ChartedSpace (Mℂ(n)) (GL (Fin n) ℂ) :=
  complexGeneralLinearGroupChartedSpace n

local notation "RealGLIsManifold(" n ")" =>
  @IsManifold ℝ inferInstance (Mℝ(n)) inferInstance inferInstance (Mℝ(n)) inferInstance
    (Iℝ(n)) ω (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)

local notation "ComplexGLIsManifold(" n ")" =>
  @IsManifold ℂ inferInstance (Mℂ(n)) inferInstance inferInstance (Mℂ(n)) inferInstance
    (Iℂ(n)) ω (GL (Fin n) ℂ) inferInstance (complexGeneralLinearGroupChartedSpace n)

local notation "RealComplexGLIsManifold(" n ")" =>
  @IsManifold ℝ inferInstance (Mℂ(n)) inferInstance inferInstance (Mℂ(n)) inferInstance
    (Iℝℂ(n)) ω (GL (Fin n) ℂ) inferInstance (complexGeneralLinearGroupChartedSpace n)

local notation "RealGLLieGroup(" n ")" =>
  @LieGroup ℝ inferInstance (Mℝ(n)) inferInstance (Mℝ(n)) inferInstance inferInstance
    (Iℝ(n)) ∞ (GL (Fin n) ℝ) inferInstance inferInstance (realGeneralLinearGroupChartedSpace n)

local notation "ComplexGLLieGroup(" n ")" =>
  @LieGroup ℂ inferInstance (Mℂ(n)) inferInstance (Mℂ(n)) inferInstance inferInstance
    (Iℂ(n)) ∞ (GL (Fin n) ℂ) inferInstance inferInstance (complexGeneralLinearGroupChartedSpace n)

local notation "RealComplexGLLieGroup(" n ")" =>
  @LieGroup ℝ inferInstance (Mℂ(n)) inferInstance (Mℂ(n)) inferInstance inferInstance
    (Iℝℂ(n)) ∞ (GL (Fin n) ℂ) inferInstance inferInstance
      (complexGeneralLinearGroupChartedSpace n)

/-- Helper for Problem 8-29: smoothness into a units type can be checked after composing with the
ambient valuation map. -/
private theorem contMDiffUnitsOfVal
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {R : Type*} [NormedRing R] [CompleteSpace R] [NormedAlgebra 𝕜 R]
    {f : M → Rˣ}
    (h : ContMDiff I (𝓘(𝕜, R)) ∞ fun x ↦ ((f x : Rˣ) : R)) :
    ContMDiff I (𝓘(𝕜, R)) ∞ f := by
  -- The units manifold is an open submanifold of the ambient normed algebra.
  refine ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val ?_
  simpa using! h

noncomputable local instance realGeneralLinearGroupLieGroup (n : ℕ) : RealGLLieGroup(n) := by
  let _ : ChartedSpace (Mℝ(n)) ((Mℝ(n))ˣ) :=
    @Units.instChartedSpace (Mℝ(n)) (real_matrix_normedRing n) (real_matrix_completeSpace n)
  -- Rewrite `GL(n, ℝ)` to the ambient units type and reuse the canonical units Lie-group owner.
  change @LieGroup
      ℝ inferInstance
      (Mℝ(n)) inferInstance
      (Mℝ(n)) inferInstance inferInstance
      (Iℝ(n)) ∞
      ((Mℝ(n))ˣ) inferInstance inferInstance inferInstance
  exact @Units.instLieGroupModelWithCornersSelf
    (Mℝ(n))
    (real_matrix_normedRing n)
    (real_matrix_completeSpace n)
    ∞
    ℝ
    inferInstance
    (real_matrix_normedAlgebra n)

noncomputable local instance realGeneralLinearGroupLieGroupTop (n : ℕ) :
    @LieGroup ℝ inferInstance
      (Mℝ(n)) inferInstance (Mℝ(n)) inferInstance inferInstance
      (Iℝ(n)) (⊤ : WithTop ℕ∞) (GL (Fin n) ℝ) inferInstance inferInstance
      (realGeneralLinearGroupChartedSpace n) := by
  -- `LieSubgroup` uses the top-regularity owner spelling, so expose that local instance directly.
  let _ : ChartedSpace (Mℝ(n)) ((Mℝ(n))ˣ) :=
    @Units.instChartedSpace (Mℝ(n)) (real_matrix_normedRing n) (real_matrix_completeSpace n)
  change @LieGroup
      ℝ inferInstance
      (Mℝ(n)) inferInstance
      (Mℝ(n)) inferInstance inferInstance
      (Iℝ(n)) (⊤ : WithTop ℕ∞)
      ((Mℝ(n))ˣ) inferInstance inferInstance inferInstance
  exact @Units.instLieGroupModelWithCornersSelf
    (Mℝ(n))
    (real_matrix_normedRing n)
    (real_matrix_completeSpace n)
    (⊤ : WithTop ℕ∞)
    ℝ
    inferInstance
    (real_matrix_normedAlgebra n)

noncomputable local instance complexGeneralLinearGroupLieGroup (n : ℕ) : ComplexGLLieGroup(n) :=
  by
  let _ : ChartedSpace (Mℂ(n)) ((Mℂ(n))ˣ) :=
    @Units.instChartedSpace (Mℂ(n)) (complex_matrix_normedRing n) (complex_matrix_completeSpace n)
  -- Rewrite `GL(n, ℂ)` to the ambient units type and reuse the canonical units Lie-group owner.
  change @LieGroup
      ℂ inferInstance
      (Mℂ(n)) inferInstance
      (Mℂ(n)) inferInstance inferInstance
      (Iℂ(n)) ∞
      ((Mℂ(n))ˣ) inferInstance inferInstance inferInstance
  exact @Units.instLieGroupModelWithCornersSelf
    (Mℂ(n))
    (complex_matrix_normedRing n)
    (complex_matrix_completeSpace n)
    ∞
    ℂ
    inferInstance
    (complex_matrix_normedAlgebra n)

noncomputable local instance complexGeneralLinearGroupLieGroupTop (n : ℕ) :
    @LieGroup ℂ inferInstance
      (Mℂ(n)) inferInstance (Mℂ(n)) inferInstance inferInstance
      (Iℂ(n)) (⊤ : WithTop ℕ∞) (GL (Fin n) ℂ) inferInstance inferInstance
      (complexGeneralLinearGroupChartedSpace n) := by
  -- `LieSubgroup` uses the top-regularity owner spelling, so expose that local instance directly.
  let _ : ChartedSpace (Mℂ(n)) ((Mℂ(n))ˣ) :=
    @Units.instChartedSpace (Mℂ(n)) (complex_matrix_normedRing n) (complex_matrix_completeSpace n)
  change @LieGroup
      ℂ inferInstance
      (Mℂ(n)) inferInstance
      (Mℂ(n)) inferInstance inferInstance
      (Iℂ(n)) (⊤ : WithTop ℕ∞)
      ((Mℂ(n))ˣ) inferInstance inferInstance inferInstance
  exact @Units.instLieGroupModelWithCornersSelf
    (Mℂ(n))
    (complex_matrix_normedRing n)
    (complex_matrix_completeSpace n)
    (⊤ : WithTop ℕ∞)
    ℂ
    inferInstance
    (complex_matrix_normedAlgebra n)

noncomputable local instance realComplexGeneralLinearGroupLieGroup (n : ℕ) :
    RealComplexGLLieGroup(n) :=
  by
  let _ : ChartedSpace (Mℂ(n)) ((Mℂ(n))ˣ) :=
    @Units.instChartedSpace (Mℂ(n)) (complex_matrix_normedRing n) (complex_matrix_completeSpace n)
  -- Rewrite `GL(n, ℂ)` to the ambient units type and reuse the real Lie-group structure on units.
  change @LieGroup
      ℝ inferInstance
      (Mℂ(n)) inferInstance
      (Mℂ(n)) inferInstance inferInstance
      (Iℝℂ(n)) ∞
      ((Mℂ(n))ˣ) inferInstance inferInstance inferInstance
  exact @Units.instLieGroupModelWithCornersSelf
    (Mℂ(n))
    (complex_matrix_normedRing n)
    (complex_matrix_completeSpace n)
    ∞
    ℝ
    inferInstance
    (inferInstance : NormedAlgebra ℝ (Mℂ(n)))

noncomputable local instance realComplexGeneralLinearGroupLieGroupTop (n : ℕ) :
    @LieGroup ℝ inferInstance
      (Mℂ(n)) inferInstance (Mℂ(n)) inferInstance inferInstance
      (Iℝℂ(n)) (⊤ : WithTop ℕ∞) (GL (Fin n) ℂ) inferInstance inferInstance
      (complexGeneralLinearGroupChartedSpace n) := by
  -- `LieSubgroup` uses the top-regularity owner spelling, so expose that local instance directly.
  let _ : ChartedSpace (Mℂ(n)) ((Mℂ(n))ˣ) :=
    @Units.instChartedSpace (Mℂ(n)) (complex_matrix_normedRing n) (complex_matrix_completeSpace n)
  change @LieGroup
      ℝ inferInstance
      (Mℂ(n)) inferInstance
      (Mℂ(n)) inferInstance inferInstance
      (Iℝℂ(n)) (⊤ : WithTop ℕ∞)
      ((Mℂ(n))ˣ) inferInstance inferInstance inferInstance
  exact @Units.instLieGroupModelWithCornersSelf
    (Mℂ(n))
    (complex_matrix_normedRing n)
    (complex_matrix_completeSpace n)
    (⊤ : WithTop ℕ∞)
    ℝ
    inferInstance
    (inferInstance : NormedAlgebra ℝ (Mℂ(n)))

/-- The canonical inclusion `SO(n) → O(n)`. -/
private def specialOrthogonalToOrthogonal (n : ℕ) : SO(n) →* O(n) where
  toFun A := ⟨A.1, A.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The canonical inclusion `SO(n) → GL(n, ℝ)`. -/
private def specialOrthogonalToGeneralLinearGroup (n : ℕ) : SO(n) →* GL (Fin n) ℝ :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) ℝ ≃*
      LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ)).symm.toMonoidHom.comp
    (Matrix.UnitaryGroup.embeddingGL :
      O(n) →* LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ))).comp
    (specialOrthogonalToOrthogonal n)

/-- Helper for Problem 8-29: the canonical inclusion `SO(n) → GL(n, ℝ)` preserves the
underlying matrix. -/
private theorem specialOrthogonalToGeneralLinearGroup_coe (n : ℕ) (A : SO(n)) :
    (((specialOrthogonalToGeneralLinearGroup n) A : GL (Fin n) ℝ) : Mℝ(n)) = (A : Mℝ(n)) := by
  -- Compare the defining monoid homomorphisms entrywise after expanding the orthogonal embedding.
  ext i j
  simp [specialOrthogonalToGeneralLinearGroup, specialOrthogonalToOrthogonal,
    Matrix.GeneralLinearGroup.toLin, Matrix.UnitaryGroup.embeddingGL,
    Matrix.UnitaryGroup.toGL, Matrix.UnitaryGroup.toLinearEquiv, Matrix.toLin'_apply]

/-- The canonical copy of `SO(n)` inside `GL(n, ℝ)`. -/
def specialOrthogonalSubgroupInGeneralLinearGroup (n : ℕ) : Subgroup (GL (Fin n) ℝ) :=
  (⊤ : Subgroup (SO(n))).map (specialOrthogonalToGeneralLinearGroup n)

/-- Helper for Problem 8-29: membership in the canonical `GL(n, ℝ)` copy of `SO(n)` is the usual
special-orthogonal matrix condition. -/
private theorem mem_specialOrthogonalSubgroupInGeneralLinearGroup_iff
    (n : ℕ) (g : GL (Fin n) ℝ) :
    g ∈ specialOrthogonalSubgroupInGeneralLinearGroup n ↔
      (g : Mℝ(n)) ∈ SO(n) := by
  constructor
  · intro hg
    rcases Subgroup.mem_map.mp hg with ⟨A, -, hA⟩
    -- Transport the special-orthogonal condition from the source matrix in `SO(n)`.
    have hMatrix : ((g : GL (Fin n) ℝ) : Mℝ(n)) = (A : Mℝ(n)) := by
      rw [← hA, specialOrthogonalToGeneralLinearGroup_coe]
    rw [hMatrix]
    exact A.property
  · intro hg
    let A : SO(n) := ⟨(g : Mℝ(n)), hg⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨A, by simp, ?_⟩
    refine (Matrix.GeneralLinearGroup.ext_iff _ _).2 ?_
    intro i j
    -- The mapped `SO(n)` element has the same ambient matrix entries as `g`.
    simpa [A] using
      congrArg (fun M : Mℝ(n) ↦ M i j) (specialOrthogonalToGeneralLinearGroup_coe n A)

/-- The canonical copy of `SL(n, ℝ)` inside `GL(n, ℝ)`. -/
abbrev specialLinearRealSubgroupInGeneralLinearGroup (n : ℕ) :
    Subgroup (GL (Fin n) ℝ) :=
  toGL.range

/-- The canonical inclusion `U(n) → GL(n, ℂ)`. -/
abbrev unitarySubgroupToGeneralLinearGroup (n : ℕ) : U(n) →* GL (Fin n) ℂ :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) ℂ ≃*
      LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ)).symm.toMonoidHom.comp
    (Matrix.UnitaryGroup.embeddingGL :
      U(n) →* LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ)))

/-- Helper for Problem 8-29: the canonical inclusion `U(n) → GL(n, ℂ)` preserves the underlying
matrix. -/
private theorem unitarySubgroupToGeneralLinearGroup_coe (n : ℕ) (A : U(n)) :
    (((unitarySubgroupToGeneralLinearGroup n) A : GL (Fin n) ℂ) : Mℂ(n)) = (A : Mℂ(n)) := by
  -- Compare the two `GL` elements entrywise after expanding the defining matrix/linear maps.
  ext i j
  simp [unitarySubgroupToGeneralLinearGroup, Matrix.GeneralLinearGroup.toLin,
    Matrix.UnitaryGroup.embeddingGL, Matrix.UnitaryGroup.toGL,
    Matrix.UnitaryGroup.toLinearEquiv, Matrix.toLin'_apply]

/-- The canonical copy of `U(n)` inside `GL(n, ℂ)`. -/
def unitarySubgroupInGeneralLinearGroup (n : ℕ) : Subgroup (GL (Fin n) ℂ) :=
  (⊤ : Subgroup (U(n))).map (unitarySubgroupToGeneralLinearGroup n)

/-- Helper for Problem 8-29: membership in the canonical `GL(n, ℂ)` copy of `U(n)` is the usual
unitary matrix equation `Aᴴ * A = 1`. -/
private theorem mem_unitarySubgroupInGeneralLinearGroup_iff
    (n : ℕ) (A : GL (Fin n) ℂ) :
    A ∈ unitarySubgroupInGeneralLinearGroup n ↔
      star (↑A : Mℂ(n)) * (↑A : Mℂ(n)) = 1 := by
  constructor
  · intro hA
    rcases Subgroup.mem_map.mp hA with ⟨U, -, hU⟩
    -- Transport the unitary equation from the source matrix `U`.
    have hMatrix : (↑A : Mℂ(n)) = (U : Mℂ(n)) := by
      rw [← hU, unitarySubgroupToGeneralLinearGroup_coe]
    rw [hMatrix]
    simpa using Matrix.UnitaryGroup.star_mul_self U
  · intro hA
    let U : U(n) := ⟨(A : Mℂ(n)), (Matrix.mem_unitaryGroup_iff').2 hA⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨U, by simp, ?_⟩
    refine (Matrix.GeneralLinearGroup.ext_iff _ _).2 ?_
    intro i j
    -- The mapped unitary matrix has the same ambient matrix entries as `A`.
    simpa [U] using
      congrArg (fun M : Mℂ(n) ↦ M i j) (unitarySubgroupToGeneralLinearGroup_coe n U)

/-- The canonical inclusion `SU(n) → U(n)`. -/
def specialUnitaryToUnitary (n : ℕ) : SU(n) →* U(n) where
  toFun A := ⟨A.1, Matrix.specialUnitaryGroup_le_unitaryGroup A.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The canonical inclusion `SU(n) → GL(n, ℂ)`. -/
private def specialUnitaryToGeneralLinearGroup (n : ℕ) : SU(n) →* GL (Fin n) ℂ :=
  (unitarySubgroupToGeneralLinearGroup n).comp (specialUnitaryToUnitary n)

/-- Helper for Problem 8-29: the canonical inclusion `SU(n) → GL(n, ℂ)` preserves the underlying
matrix. -/
private theorem specialUnitaryToGeneralLinearGroup_coe (n : ℕ) (A : SU(n)) :
    (((specialUnitaryToGeneralLinearGroup n) A : GL (Fin n) ℂ) : Mℂ(n)) = (A : Mℂ(n)) := by
  -- The `SU(n)` inclusion factors through `U(n)` without changing the matrix entries.
  simpa [specialUnitaryToGeneralLinearGroup, specialUnitaryToUnitary] using
    unitarySubgroupToGeneralLinearGroup_coe n (specialUnitaryToUnitary n A)

/-- The canonical copy of `SU(n)` inside `GL(n, ℂ)`. -/
def specialUnitarySubgroupInGeneralLinearGroup (n : ℕ) : Subgroup (GL (Fin n) ℂ) :=
  (⊤ : Subgroup (SU(n))).map (specialUnitaryToGeneralLinearGroup n)

/-- Helper for Problem 8-29: membership in the canonical `GL(n, ℂ)` copy of `SU(n)` means
unitary together with determinant one. -/
private theorem mem_specialUnitarySubgroupInGeneralLinearGroup_iff_mem_unitary_det_eq_one
    (n : ℕ) (g : GL (Fin n) ℂ) :
    g ∈ specialUnitarySubgroupInGeneralLinearGroup n ↔
      g ∈ unitarySubgroupInGeneralLinearGroup n ∧ Matrix.GeneralLinearGroup.det g = 1 := by
  constructor
  · intro hg
    rcases Subgroup.mem_map.mp hg with ⟨A, -, hA⟩
    constructor
    · -- Forgetting determinant one leaves ordinary unitary membership.
      refine Subgroup.mem_map.mpr ?_
      refine ⟨specialUnitaryToUnitary n A, by simp, ?_⟩
      simpa [specialUnitaryToGeneralLinearGroup] using hA
    · -- The determinant is transported from the defining `SU(n)` condition.
      rw [← hA]
      apply Units.ext
      simpa [specialUnitaryToGeneralLinearGroup_coe] using A.2.2
  · rintro ⟨hgU, hgdet⟩
    have hgSU : (g : Mℂ(n)) ∈ SU(n) := by
      refine (Matrix.mem_specialUnitaryGroup_iff).2 ?_
      constructor
      · rw [Matrix.mem_unitaryGroup_iff']
        exact (mem_unitarySubgroupInGeneralLinearGroup_iff n g).1 hgU
      · simpa using congrArg Units.val hgdet
    let A : SU(n) := ⟨(g : Mℂ(n)), hgSU⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨A, by simp, ?_⟩
    refine (Matrix.GeneralLinearGroup.ext_iff _ _).2 ?_
    intro i j
    -- The mapped `SU(n)` element has the same ambient matrix entries as `g`.
    simpa [A] using
      congrArg (fun M : Mℂ(n) ↦ M i j) (specialUnitaryToGeneralLinearGroup_coe n A)

/-- The canonical copy of `SL(n, ℂ)` inside `GL(n, ℂ)`. -/
abbrev specialLinearComplexSubgroupInGeneralLinearGroup (n : ℕ) :
    Subgroup (GL (Fin n) ℂ) :=
  toGL.range

/-- The skew-Hermitian predicate cutting out the real matrix Lie algebra `𝔲(n)`. -/
private def is_unitary_matrix_lie (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Aᴴ = -A

/-- Zero is skew-Hermitian. -/
private theorem is_unitary_matrix_lie_zero (n : ℕ) :
    is_unitary_matrix_lie n (0 : Matrix (Fin n) (Fin n) ℂ) := by
  -- The zero matrix satisfies the defining skew-Hermitian equation by direct simplification.
  simp [is_unitary_matrix_lie]

/-- The skew-Hermitian matrices are closed under addition. -/
private theorem is_unitary_matrix_lie_add (n : ℕ) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : is_unitary_matrix_lie n A) (hB : is_unitary_matrix_lie n B) :
    is_unitary_matrix_lie n (A + B) := by
  -- Conjugate transpose is additive, so the defining equation rewrites termwise.
  rw [is_unitary_matrix_lie] at hA hB ⊢
  rw [Matrix.conjTranspose_add, hA, hB]
  abel

/-- The skew-Hermitian matrices are closed under real scalar multiplication. -/
private theorem is_unitary_matrix_lie_real_smul (n : ℕ) (r : ℝ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : is_unitary_matrix_lie n A) :
    is_unitary_matrix_lie n (r • A) := by
  -- Real scalars are fixed by conjugation, so skew-Hermitianity is preserved under `ℝ`-scaling.
  rw [is_unitary_matrix_lie] at hA ⊢
  simpa using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ ↦ r • M) hA

/-- The skew-Hermitian matrices are closed under the commutator bracket. -/
private theorem is_unitary_matrix_lie_lie (n : ℕ) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : is_unitary_matrix_lie n A) (hB : is_unitary_matrix_lie n B) :
    is_unitary_matrix_lie n ⁅A, B⁆ := by
  -- The adjoint reverses products, so the commutator picks up a minus sign.
  rw [is_unitary_matrix_lie] at hA hB ⊢
  calc
    (⁅A, B⁆ : Matrix (Fin n) (Fin n) ℂ)ᴴ = Bᴴ * Aᴴ - Aᴴ * Bᴴ := by
      simp [Ring.lie_def]
    _ = B * A - A * B := by rw [hA, hB]; simp
    _ = -(A * B - B * A) := by
      abel
    _ = -(⁅A, B⁆ : Matrix (Fin n) (Fin n) ℂ) := by rw [Ring.lie_def]

/-- The real matrix Lie algebra `𝔲(n)`, realized as the skew-Hermitian `n x n` complex matrices.
-/
def unitary_matrix_lie_subalgebra (n : ℕ) : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | is_unitary_matrix_lie n A}
  zero_mem' := is_unitary_matrix_lie_zero n
  add_mem' := fun hA hB ↦ is_unitary_matrix_lie_add n hA hB
  smul_mem' := fun r _ hA ↦ is_unitary_matrix_lie_real_smul n r hA
  lie_mem' := fun hA hB ↦ is_unitary_matrix_lie_lie n hA hB

/-- Membership in `unitary_matrix_lie_subalgebra n` is the skew-Hermitian condition `Aᴴ = -A`. -/
theorem unitary_matrix_lie_subalgebra_mem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ unitary_matrix_lie_subalgebra n ↔ Aᴴ = -A := by
  -- This is exactly the carrier predicate used in the definition.
  rfl

/-- The skew-Hermitian trace-zero predicate cutting out the real matrix Lie algebra `𝔰𝔲(n)`. -/
private def is_special_unitary_matrix_lie (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Aᴴ = -A ∧ Matrix.trace A = 0

/-- Zero is skew-Hermitian and trace zero. -/
private theorem is_special_unitary_matrix_lie_zero (n : ℕ) :
    is_special_unitary_matrix_lie n (0 : Matrix (Fin n) (Fin n) ℂ) := by
  -- Both defining conditions are immediate for the zero matrix.
  simp [is_special_unitary_matrix_lie]

/-- The skew-Hermitian trace-zero matrices are closed under addition. -/
private theorem is_special_unitary_matrix_lie_add (n : ℕ)
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : is_special_unitary_matrix_lie n A) (hB : is_special_unitary_matrix_lie n B) :
    is_special_unitary_matrix_lie n (A + B) := by
  rcases hA with ⟨hA_skew, hA_trace⟩
  rcases hB with ⟨hB_skew, hB_trace⟩
  -- Both the skew-Hermitian and trace-zero conditions are additive.
  constructor
  · exact is_unitary_matrix_lie_add n hA_skew hB_skew
  · simp [Matrix.trace_add, hA_trace, hB_trace]

/-- The skew-Hermitian trace-zero matrices are closed under real scalar multiplication. -/
private theorem is_special_unitary_matrix_lie_real_smul (n : ℕ) (r : ℝ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : is_special_unitary_matrix_lie n A) :
    is_special_unitary_matrix_lie n (r • A) := by
  rcases hA with ⟨hA_skew, hA_trace⟩
  -- Real scalar multiplication preserves both defining conditions.
  constructor
  · exact is_unitary_matrix_lie_real_smul n r hA_skew
  · simp [Matrix.trace_smul, hA_trace]

/-- The skew-Hermitian trace-zero matrices are closed under the commutator bracket. -/
private theorem is_special_unitary_matrix_lie_lie (n : ℕ) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : is_special_unitary_matrix_lie n A) (hB : is_special_unitary_matrix_lie n B) :
    is_special_unitary_matrix_lie n ⁅A, B⁆ := by
  rcases hA with ⟨hA_skew, _hA_trace⟩
  rcases hB with ⟨hB_skew, _hB_trace⟩
  -- The commutator stays skew-Hermitian, and its trace vanishes by the standard trace identity.
  constructor
  · exact is_unitary_matrix_lie_lie n hA_skew hB_skew
  · exact
      (LieAlgebra.matrix_trace_commutator_zero (Fin n) ℂ A B)

/-- The real matrix Lie algebra `𝔰𝔲(n)`, realized as the trace-zero skew-Hermitian `n x n`
complex matrices. -/
def special_unitary_matrix_lie_subalgebra (n : ℕ) :
    LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | is_special_unitary_matrix_lie n A}
  zero_mem' := is_special_unitary_matrix_lie_zero n
  add_mem' := fun hA hB ↦ is_special_unitary_matrix_lie_add n hA hB
  smul_mem' := fun r _ hA ↦ is_special_unitary_matrix_lie_real_smul n r hA
  lie_mem' := fun hA hB ↦ is_special_unitary_matrix_lie_lie n hA hB

/-- Membership in `special_unitary_matrix_lie_subalgebra n` is the condition
`Aᴴ = -A ∧ Matrix.trace A = 0`. -/
theorem special_unitary_matrix_lie_subalgebra_mem
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ special_unitary_matrix_lie_subalgebra n ↔ Aᴴ = -A ∧ Matrix.trace A = 0 := by
  -- This is exactly the carrier predicate used in the definition.
  rfl

/-- Helper for Problem 8-29: membership in `𝔰𝔩(n, R)` is exactly the trace-zero condition. -/
private theorem mem_specialLinearLieSubalgebra_iff_trace_eq_zero
    {R : Type*} [CommRing R] (n : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    A ∈ LieAlgebra.SpecialLinear.sl (Fin n) R ↔ Matrix.trace A = 0 := by
  -- Expand `sl` as the kernel of the trace linear map, so membership is exactly trace zero.
  rw [LieAlgebra.SpecialLinear.sl]
  rfl

/-- Helper for Problem 8-29: the canonical `SL(n, ℝ)` copy inside `GL(n, ℝ)` is the determinant
kernel. -/
private theorem specialLinearRealSubgroupInGeneralLinearGroup_eq_det_ker
    (n : ℕ) :
    specialLinearRealSubgroupInGeneralLinearGroup n =
      (Matrix.GeneralLinearGroup.det : GL (Fin n) ℝ →* ℝˣ).ker := by
  ext g
  -- Rewrite the subgroup range through the standard description of `SL → GL` as `det = 1`.
  change g ∈ Set.range
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin n) ℝ → GL (Fin n) ℝ) ↔
    g ∈ (Matrix.GeneralLinearGroup.det : GL (Fin n) ℝ →* ℝˣ).ker
  rw [Matrix.SpecialLinearGroup.range_toGL]
  -- Kernel membership is exactly the same `det = 1` condition.
  simp [MonoidHom.mem_ker]

/-- Helper for Problem 8-29: the canonical `SL(n, ℂ)` copy inside `GL(n, ℂ)` is the determinant
kernel. -/
private theorem specialLinearComplexSubgroupInGeneralLinearGroup_eq_det_ker
    (n : ℕ) :
    specialLinearComplexSubgroupInGeneralLinearGroup n =
      (Matrix.GeneralLinearGroup.det : GL (Fin n) ℂ →* ℂˣ).ker := by
  ext g
  -- Rewrite the subgroup range through the standard description of `SL → GL` as `det = 1`.
  change g ∈ Set.range
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin n) ℂ → GL (Fin n) ℂ) ↔
    g ∈ (Matrix.GeneralLinearGroup.det : GL (Fin n) ℂ →* ℂˣ).ker
  rw [Matrix.SpecialLinearGroup.range_toGL]
  -- Kernel membership is exactly the same `det = 1` condition.
  simp [MonoidHom.mem_ker]

/-- Helper for Problem 8-29: when `n > 0`, a diagonal matrix supported at one index has the
prescribed trace. -/
private theorem trace_diagonal_supportedAtZero
    {R : Type*} [Semiring R] (n : ℕ) (hn : 0 < n) (c : R) :
    Matrix.trace
        (Matrix.diagonal fun j : Fin n ↦ if j = ⟨0, hn⟩ then c else 0) = c := by
  -- The diagonal sum has exactly one nonzero contribution, at the chosen index `0`.
  rw [Matrix.trace_diagonal]
  simpa using Finset.sum_ite_eq' Finset.univ ⟨0, hn⟩ c

/-- Helper for Problem 8-29: the matrix Lie algebra `𝔬(n)` is cut out by the equation
`Aᵀ + A = 0`. -/
private theorem mem_orthogonalLieSubalgebra_iff_transpose_add_eq_zero
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ ↔ A.transpose + A = 0 := by
  -- Convert the standard skew-symmetry characterization into the additive normal form used later.
  rw [LieAlgebra.Orthogonal.mem_so]
  constructor
  · intro hA
    calc
      A.transpose + A = -A + A := by rw [hA]
      _ = 0 := by simp
  · intro hA
    simpa using eq_neg_of_add_eq_zero_left hA

/-- Helper for Problem 8-29: the Lie bracket in a matrix algebra is the associative commutator. -/
private theorem matrixLieBracket_eq_commutator
    {R : Type*} [CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) :
    (⁅A, B⁆ : Matrix (Fin n) (Fin n) R) = A * B - B * A := by
  rw [Ring.lie_def]

/-- Helper for Problem 8-29: the `(i,j)` entry of a matrix Lie bracket is the corresponding
entry of the associative commutator. -/
private theorem matrixLieBracket_entry_eq_commutator
    {R : Type*} [CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (⁅A, B⁆ : Matrix (Fin n) (Fin n) R) i j =
      (A * B) i j - (B * A) i j := by
  -- Apply the ambient commutator formula entrywise.
  simpa using
    congrArg (fun M : Matrix (Fin n) (Fin n) R ↦ M i j)
      (matrixLieBracket_eq_commutator A B)

/-- Helper for Problem 8-29: coercing the bracket in a matrix Lie subalgebra forgets only the
subtype wrapper. -/
private theorem lieSubalgebra_coe_bracket
    {R : Type*} [CommRing R] {n : ℕ}
    {L : LieSubalgebra R (Matrix (Fin n) (Fin n) R)} (A B : L) :
    ((⁅A, B⁆ : L) : Matrix (Fin n) (Fin n) R) =
      (⁅(A : Matrix (Fin n) (Fin n) R), (B : Matrix (Fin n) (Fin n) R)⁆ :
        Matrix (Fin n) (Fin n) R) := by
  rfl

/-- Helper for Problem 8-29: the value of a bracket in a matrix Lie subalgebra is the ambient
matrix commutator of the values. -/
private theorem lieSubalgebra_bracket_val
    {R : Type*} [CommRing R] {n : ℕ}
    {L : LieSubalgebra R (Matrix (Fin n) (Fin n) R)} (A B : L) :
    (⁅A, B⁆ : L).1 =
      (⁅(A : Matrix (Fin n) (Fin n) R), (B : Matrix (Fin n) (Fin n) R)⁆ :
        Matrix (Fin n) (Fin n) R) := by
  rfl

/- The next lemmas compute the first-order equations used for the classical matrix groups.  The
determinant calculation is deliberately made at the identity only; this avoids requiring a
general Jacobi formula. -/

/- Superseded: the determinant block is elaborated above, before the operator-norm instances, to
avoid typeclass-coherence problems between the two equivalent finite-dimensional matrix norms.
private noncomputable def matrixTraceContinuousLinearMap
    {R : Type*} [NontriviallyNormedField R] [CompleteSpace R]
    (n : ℕ) [NormedRing (Matrix (Fin n) (Fin n) R)]
    [NormedAlgebra R (Matrix (Fin n) (Fin n) R)] :
    Matrix (Fin n) (Fin n) R →L[R] R :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin n) R R)

attribute [-instance] LieRing.ofAssociativeRing in
private theorem matrixDet_differentiableAt_one
    {R : Type*} [NontriviallyNormedField R] [CompleteSpace R]
    (n : ℕ) [NormedRing (Matrix (Fin n) (Fin n) R)]
    [NormedAlgebra R (Matrix (Fin n) (Fin n) R)] :
    DifferentiableAt R
      (Matrix.det : Matrix (Fin n) (Fin n) R → R) 1 := by
  let detContinuous : (Fin n → R) [⋀^(Fin n)]→L[R] R :=
    { toContinuousMultilinearMap :=
        { toMultilinearMap :=
            (Matrix.detRowAlternating : (Fin n → R) [⋀^(Fin n)]→ₗ[R] R).toMultilinearMap
          cont := by
            change Continuous
              (fun M : Matrix (Fin n) (Fin n) R ↦ Matrix.det M)
            exact Continuous.matrix_det continuous_id }
      map_eq_zero_of_eq' :=
        (Matrix.detRowAlternating :
          (Fin n → R) [⋀^(Fin n)]→ₗ[R] R).map_eq_zero_of_eq' }
  have h := detContinuous.differentiable (1 : Matrix (Fin n) (Fin n) R)
  simpa [detContinuous] using! h

attribute [-instance] LieRing.ofAssociativeRing in
private theorem matrixDet_polynomialLine
    {R : Type*} [NontriviallyNormedField R]
    (n : ℕ) [NormedRing (Matrix (Fin n) (Fin n) R)]
    [NormedAlgebra R (Matrix (Fin n) (Fin n) R)]
    (X : Matrix (Fin n) (Fin n) R) :
    (fun t : R ↦ Matrix.det (1 + t • X)) =
      fun t ↦ Polynomial.eval t
        (((1 : Matrix (Fin n) (Fin n) (Polynomial R)) +
          (Polynomial.X : Polynomial R) • X.map Polynomial.C).det) := by
  funext t
  change (1 + t • X).det =
    (Polynomial.evalRingHom t)
      (((1 : Matrix (Fin n) (Fin n) (Polynomial R)) +
        (Polynomial.X : Polynomial R) • X.map Polynomial.C).det)
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, map_add, map_mul]
  rw [mul_comm t (X i j)]
  change (1 : Matrix (Fin n) (Fin n) R) i j + X i j * t =
    Polynomial.eval t ((1 : Matrix (Fin n) (Fin n) (Polynomial R)) i j) +
      Polynomial.eval t Polynomial.X * Polynomial.eval t (Polynomial.C (X i j))
  rw [Polynomial.eval_X, Polynomial.eval_C, mul_comm]
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Polynomial.eval_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, Polynomial.eval_zero]

attribute [-instance] LieRing.ofAssociativeRing in
private theorem matrixDet_line_hasDerivAt
    {R : Type*} [NontriviallyNormedField R]
    (n : ℕ) [NormedRing (Matrix (Fin n) (Fin n) R)]
    [NormedAlgebra R (Matrix (Fin n) (Fin n) R)]
    (X : Matrix (Fin n) (Fin n) R) :
    HasDerivAt (fun t : R ↦ Matrix.det (1 + t • X)) (Matrix.trace X) 0 := by
  rw [matrixDet_polynomialLine n X]
  convert
    (Polynomial.hasDerivAt
      (((1 : Matrix (Fin n) (Fin n) (Polynomial R)) +
        (Polynomial.X : Polynomial R) • X.map Polynomial.C).det) 0) using 1
  exact (Matrix.derivative_det_one_add_X_smul X).symm

attribute [-instance] LieRing.ofAssociativeRing real_matrix_normedRing
  real_matrix_normedAlgebra complex_matrix_normedRing complex_matrix_normedAlgebra in
private theorem matrixDet_fderiv_one_apply
    {R : Type*} [NontriviallyNormedField R] [CompleteSpace R]
    (n : ℕ) [hNR : NormedRing (Matrix (Fin n) (Fin n) R)]
    [hNA : NormedAlgebra R (Matrix (Fin n) (Fin n) R)]
    (X : Matrix (Fin n) (Fin n) R) :
    fderiv R (Matrix.det : Matrix (Fin n) (Fin n) R → R) 1 X =
      Matrix.trace X := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) R) :=
    hNR.toNormedAddCommGroup
  letI : NormedSpace R (Matrix (Fin n) (Fin n) R) := hNA.toNormedSpace
  have hd := (matrixDet_differentiableAt_one (R := R) n).hasFDerivAt
  let line : R →L[R] Matrix (Fin n) (Fin n) R :=
    LinearMap.toContinuousLinearMap
      { toFun := fun t ↦ t • X
        map_add' := fun a b ↦ add_smul a b X
        map_smul' := fun a b ↦ mul_smul a b X }
  have hlineLinear :
      HasFDerivAt (fun t : R ↦ t • X) line 0 := by
    simpa [line] using! line.hasFDerivAt
  have hinnerRaw := hlineLinear.add_const (1 : Matrix (Fin n) (Fin n) R)
  have hinner :
      HasFDerivAt
        (fun t : R ↦ (1 : Matrix (Fin n) (Fin n) R) + t • X)
        line 0 := by
    simpa [add_comm] using! hinnerRaw
  have hd' :
      HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) R → R)
        (fderiv R (Matrix.det : Matrix (Fin n) (Fin n) R → R) 1)
        ((fun t : R ↦ (1 : Matrix (Fin n) (Fin n) R) + t • X) 0) := by
    simpa using! hd
  have hcF :
      HasFDerivAt
        ((Matrix.det : Matrix (Fin n) (Fin n) R → R) ∘
          fun t : R ↦ (1 : Matrix (Fin n) (Fin n) R) + t • X)
        ((fderiv R (Matrix.det : Matrix (Fin n) (Fin n) R → R) 1).comp line) 0 :=
    hd'.comp 0 hinner
  have hc := hcF.hasDerivAt
  have hline :
      HasDerivAt (fun t : R ↦ Matrix.det (1 + t • X))
        ((fderiv R (Matrix.det : Matrix (Fin n) (Fin n) R → R) 1) X) 0 := by
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply, line, one_smul] using! hc
  exact (hline.unique (matrixDet_line_hasDerivAt (R := R) n X)).symm

attribute [-instance] LieRing.ofAssociativeRing real_matrix_normedRing
  real_matrix_normedAlgebra complex_matrix_normedRing complex_matrix_normedAlgebra in
private theorem matrixDet_hasFDerivAt_one
    {R : Type*} [NontriviallyNormedField R] [CompleteSpace R]
    (n : ℕ) [NormedRing (Matrix (Fin n) (Fin n) R)]
    [NormedAlgebra R (Matrix (Fin n) (Fin n) R)] :
    HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) R → R)
      (matrixTraceContinuousLinearMap n) 1 := by
  have hd := (matrixDet_differentiableAt_one (R := R) n).hasFDerivAt
  apply hd.congr_fderiv
  ext X
  exact matrixDet_fderiv_one_apply (R := R) n X
-/

private noncomputable def realMatrixGramRawDerivAtOne (n : ℕ) :
    Mℝ(n) →L[ℝ] Mℝ(n) :=
  ContinuousLinearMap.id ℝ (Mℝ(n)) +
    transposeContinuousLinearMap n

private theorem realMatrixGramRawDerivAtOne_apply (n : ℕ) (X : Mℝ(n)) :
    realMatrixGramRawDerivAtOne n X = X.transpose + X := by
  simp [realMatrixGramRawDerivAtOne, ContinuousLinearMap.smulRight_apply,
    transposeContinuousLinearMap_apply, add_comm]

attribute [-instance] LieRing.ofAssociativeRing in
private theorem realMatrixGram_hasFDerivAt_one (n : ℕ) :
    HasFDerivAt (fun A : Mℝ(n) ↦ A.transpose * A)
      (realMatrixGramRawDerivAtOne n) 1 := by
  have hT : HasFDerivAt (fun A : Mℝ(n) ↦ A.transpose)
      (transposeContinuousLinearMap n) 1 := by
    simpa using! (transposeContinuousLinearMap n).hasFDerivAt
  simpa [realMatrixGramRawDerivAtOne, ContinuousLinearMap.smulRight_apply] using!
    (hT.mul' (ContinuousLinearMap.id ℝ (Mℝ(n))).hasFDerivAt)

private noncomputable def matrixConjTransposeRealContinuousLinearMap (n : ℕ) :
    Mℂ(n) →L[ℝ] Mℂ(n) :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := by
        intro r A
        simpa using Matrix.conjTranspose_smul (R := ℝ) r A }

private noncomputable def complexMatrixGramRawDerivAtOne (n : ℕ) :
    Mℂ(n) →L[ℝ] Mℂ(n) :=
  ContinuousLinearMap.id ℝ (Mℂ(n)) +
    matrixConjTransposeRealContinuousLinearMap n

private theorem complexMatrixGramRawDerivAtOne_apply (n : ℕ) (X : Mℂ(n)) :
    complexMatrixGramRawDerivAtOne n X = Xᴴ + X := by
  simp [complexMatrixGramRawDerivAtOne, ContinuousLinearMap.smulRight_apply,
    matrixConjTransposeRealContinuousLinearMap, add_comm]

attribute [-instance] LieRing.ofAssociativeRing in
private theorem complexMatrixGram_hasFDerivAt_one (n : ℕ) :
    HasFDerivAt (fun A : Mℂ(n) ↦ Aᴴ * A)
      (complexMatrixGramRawDerivAtOne n) 1 := by
  have hStar : HasFDerivAt (fun A : Mℂ(n) ↦ Aᴴ)
      (matrixConjTransposeRealContinuousLinearMap n) 1 := by
    simpa [matrixConjTransposeRealContinuousLinearMap] using!
      (matrixConjTransposeRealContinuousLinearMap n).hasFDerivAt
  simpa [complexMatrixGramRawDerivAtOne, ContinuousLinearMap.smulRight_apply] using!
    (hStar.mul' (ContinuousLinearMap.id ℝ (Mℂ(n))).hasFDerivAt)

/-- A smooth function that is constant on a Lie subgroup has zero derivative on the image of the
subgroup tangent space. -/
private theorem mfderiv_eq_zero_on_groupLieSubalgebra
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (⊤ : WithTop ℕ∞) G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace]
    (f : G → F)
    (hf : MDifferentiableAt I (𝓘(𝕜, F)) f 1)
    (hconst : ∀ x : S.carrier, f x.1 = f 1)
    {A : GroupLieAlgebra I G} (hA : A ∈ LieSubgroup.groupLieSubalgebra S) :
    mfderiv I (𝓘(𝕜, F)) f 1 A = 0 := by
  have hex :
      ∃ v : TangentSpace (modelWithCornersSelf 𝕜 S.ModelSpace) (1 : S.carrier),
        mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) I
          (Subtype.val : S.carrier → G) 1 v = A :=
    (LieSubgroup.mem_groupLieSubalgebra_iff_exists_subgroupTangent S A).mp hA
  rcases hex with ⟨v, hv⟩
  have hsub :
      MDifferentiableAt (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (Subtype.val : S.carrier → G) 1 :=
    (LieSubgroup.contMDiff_subtype_val S).mdifferentiableAt (by simp)
  have hcomp :=
    mfderiv_comp_apply_of_eq (1 : S.carrier) hf hsub (by rfl) v
  have heq : f ∘ (Subtype.val : S.carrier → G) = fun _ ↦ f 1 := by
    funext x
    exact hconst x
  have hzero :
      mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) (𝓘(𝕜, F))
        (f ∘ (Subtype.val : S.carrier → G)) 1 v = 0 := by
    rw [heq, mfderiv_const]
    rfl
  calc
    mfderiv I (𝓘(𝕜, F)) f 1 A =
        mfderiv I (𝓘(𝕜, F)) f 1
          (mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) I
            (Subtype.val : S.carrier → G) 1 v) := by rw [hv]
    _ = mfderiv (modelWithCornersSelf 𝕜 S.ModelSpace) (𝓘(𝕜, F))
          (f ∘ (Subtype.val : S.carrier → G)) 1 v := by
      simpa using! hcomp.symm
    _ = 0 := hzero

/-- The units chart identifies the derivative of the real matrix-group inclusion with the
identity map. -/
private theorem realGeneralLinearGroup_val_mfderiv_eq_id
    (n : ℕ) (g : GL (Fin n) ℝ) :
    mfderiv (Iℝ(n)) (Iℝ(n)) (fun h : GL (Fin n) ℝ ↦ (h : Mℝ(n))) g =
      ContinuousLinearMap.id ℝ (Mℝ(n)) := by
  have hchart :
      extChartAt (Iℝ(n)) g = fun h : GL (Fin n) ℝ ↦ (h : Mℝ(n)) := by
    funext h
    rfl
  rw [← hchart]
  simpa using! (mfderiv_extChartAt_self (I := Iℝ(n)) (x := g))

/-- The complex units chart has identity derivative over the complex numbers. -/
private theorem complexGeneralLinearGroup_val_mfderiv_eq_id
    (n : ℕ) (g : GL (Fin n) ℂ) :
    mfderiv (Iℂ(n)) (Iℂ(n)) (fun h : GL (Fin n) ℂ ↦ (h : Mℂ(n))) g =
      ContinuousLinearMap.id ℂ (Mℂ(n)) := by
  have hchart :
      extChartAt (Iℂ(n)) g = fun h : GL (Fin n) ℂ ↦ (h : Mℂ(n)) := by
    funext h
    rfl
  rw [← hchart]
  simpa using! (mfderiv_extChartAt_self (I := Iℂ(n)) (x := g))

/-- The complex units chart also has identity derivative for the underlying real manifold. -/
private theorem realComplexGeneralLinearGroup_val_mfderiv_eq_id
    (n : ℕ) (g : GL (Fin n) ℂ) :
    mfderiv (Iℝℂ(n)) (Iℝℂ(n)) (fun h : GL (Fin n) ℂ ↦ (h : Mℂ(n))) g =
      ContinuousLinearMap.id ℝ (Mℂ(n)) := by
  have hchart :
      extChartAt (Iℝℂ(n)) g = fun h : GL (Fin n) ℂ ↦ (h : Mℂ(n)) := by
    funext h
    rfl
  rw [← hchart]
  simpa using! (mfderiv_extChartAt_self (I := Iℝℂ(n)) (x := g))

/-- The differential of determinant on the real general linear group at the identity is trace. -/
private theorem realGeneralLinearGroup_det_mfderiv_one_apply
    (n : ℕ) (A : Mℝ(n)) :
    mfderiv (Iℝ(n)) (𝓘(ℝ))
      (fun g : GL (Fin n) ℝ ↦ Matrix.det (g : Mℝ(n))) 1 A =
        Matrix.trace A := by
  have hdet :=
    (matrixDet_hasFDerivAt_one (R := ℝ) n).hasMFDerivAt
  have hdetDiff :
      MDifferentiableAt (Iℝ(n)) (𝓘(ℝ))
        (Matrix.det : Mℝ(n) → ℝ) 1 :=
    hdet.mdifferentiableAt
  have hvalDiff :
      MDifferentiableAt (Iℝ(n)) (Iℝ(n))
        (fun g : GL (Fin n) ℝ ↦ (g : Mℝ(n))) 1 := by
    have hchart :
        (fun g : GL (Fin n) ℝ ↦ (g : Mℝ(n))) =
          extChartAt (Iℝ(n)) (1 : GL (Fin n) ℝ) := by
      funext g
      rfl
    rw [hchart]
    exact mdifferentiableAt_extChartAt (by simp)
  have hcomp :=
    mfderiv_comp_apply_of_eq (1 : GL (Fin n) ℝ) hdetDiff hvalDiff (by rfl) A
  rw [realGeneralLinearGroup_val_mfderiv_eq_id] at hcomp
  have hambient :=
    congrArg (fun L : Mℝ(n) →L[ℝ] ℝ ↦ L A) hdet.mfderiv
  calc
    mfderiv (Iℝ(n)) (𝓘(ℝ))
        (fun g : GL (Fin n) ℝ ↦ Matrix.det (g : Mℝ(n))) 1 A =
        mfderiv (Iℝ(n)) (𝓘(ℝ)) (Matrix.det : Mℝ(n) → ℝ) 1 A := by
      simpa [Function.comp_def] using! hcomp
    _ = Matrix.trace A := by
      simpa [matrixTraceContinuousLinearMap] using! hambient

/-- The differential of determinant on the complex general linear group at the identity is
complex trace. -/
private theorem complexGeneralLinearGroup_det_mfderiv_one_apply
    (n : ℕ) (A : Mℂ(n)) :
    mfderiv (Iℂ(n)) (𝓘(ℂ))
      (fun g : GL (Fin n) ℂ ↦ Matrix.det (g : Mℂ(n))) 1 A =
        Matrix.trace A := by
  have hdet :=
    (matrixDet_hasFDerivAt_one (R := ℂ) n).hasMFDerivAt
  have hdetDiff :
      MDifferentiableAt (Iℂ(n)) (𝓘(ℂ))
        (Matrix.det : Mℂ(n) → ℂ) 1 :=
    hdet.mdifferentiableAt
  have hvalDiff :
      MDifferentiableAt (Iℂ(n)) (Iℂ(n))
        (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) 1 := by
    have hchart :
        (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) =
          extChartAt (Iℂ(n)) (1 : GL (Fin n) ℂ) := by
      funext g
      rfl
    rw [hchart]
    exact mdifferentiableAt_extChartAt (by simp)
  have hcomp :=
    mfderiv_comp_apply_of_eq (1 : GL (Fin n) ℂ) hdetDiff hvalDiff (by rfl) A
  rw [complexGeneralLinearGroup_val_mfderiv_eq_id] at hcomp
  have hambient :=
    congrArg (fun L : Mℂ(n) →L[ℂ] ℂ ↦ L A) hdet.mfderiv
  calc
    mfderiv (Iℂ(n)) (𝓘(ℂ))
        (fun g : GL (Fin n) ℂ ↦ Matrix.det (g : Mℂ(n))) 1 A =
        mfderiv (Iℂ(n)) (𝓘(ℂ)) (Matrix.det : Mℂ(n) → ℂ) 1 A := by
      simpa [Function.comp_def] using! hcomp
    _ = Matrix.trace A := by
      simpa [matrixTraceContinuousLinearMap] using! hambient

/-- The same determinant differential after restricting scalars to the underlying real
manifold. -/
private theorem realComplexGeneralLinearGroup_det_mfderiv_one_apply
    (n : ℕ) (A : Mℂ(n)) :
    mfderiv (Iℝℂ(n)) (𝓘(ℝ, ℂ))
      (fun g : GL (Fin n) ℂ ↦ Matrix.det (g : Mℂ(n))) 1 A =
        Matrix.trace A := by
  have hdet :=
    (matrixDet_hasFDerivAt_one (R := ℂ) n).restrictScalars ℝ
  have hdetDiff :
      MDifferentiableAt (Iℝℂ(n)) (𝓘(ℝ, ℂ))
        (Matrix.det : Mℂ(n) → ℂ) 1 :=
    hdet.hasMFDerivAt.mdifferentiableAt
  have hvalDiff :
      MDifferentiableAt (Iℝℂ(n)) (Iℝℂ(n))
        (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) 1 := by
    have hchart :
        (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) =
          extChartAt (Iℝℂ(n)) (1 : GL (Fin n) ℂ) := by
      funext g
      rfl
    rw [hchart]
    exact mdifferentiableAt_extChartAt (by simp)
  have hcomp :=
    mfderiv_comp_apply_of_eq (1 : GL (Fin n) ℂ) hdetDiff hvalDiff (by rfl) A
  rw [realComplexGeneralLinearGroup_val_mfderiv_eq_id] at hcomp
  have hambient :=
    congrArg (fun L : Mℂ(n) →L[ℝ] ℂ ↦ L A) hdet.hasMFDerivAt.mfderiv
  calc
    mfderiv (Iℝℂ(n)) (𝓘(ℝ, ℂ))
        (fun g : GL (Fin n) ℂ ↦ Matrix.det (g : Mℂ(n))) 1 A =
        mfderiv (Iℝℂ(n)) (𝓘(ℝ, ℂ)) (Matrix.det : Mℂ(n) → ℂ) 1 A := by
      simpa [Function.comp_def] using! hcomp
    _ = Matrix.trace A := by
      simpa [matrixTraceContinuousLinearMap] using! hambient

/-- The Gram-map differential on the real general linear group is transpose plus identity. -/
private theorem realGeneralLinearGroup_gram_mfderiv_one_apply
    (n : ℕ) (A : Mℝ(n)) :
    mfderiv (Iℝ(n)) (Iℝ(n))
      (fun g : GL (Fin n) ℝ ↦ (g : Mℝ(n)).transpose * (g : Mℝ(n))) 1 A =
        A.transpose + A := by
  have hgram := (realMatrixGram_hasFDerivAt_one n).hasMFDerivAt
  have hgramDiff :
      MDifferentiableAt (Iℝ(n)) (Iℝ(n))
        (fun B : Mℝ(n) ↦ B.transpose * B) 1 :=
    hgram.mdifferentiableAt
  have hvalDiff :
      MDifferentiableAt (Iℝ(n)) (Iℝ(n))
        (fun g : GL (Fin n) ℝ ↦ (g : Mℝ(n))) 1 := by
    have hchart :
        (fun g : GL (Fin n) ℝ ↦ (g : Mℝ(n))) =
          extChartAt (Iℝ(n)) (1 : GL (Fin n) ℝ) := by
      funext g
      rfl
    rw [hchart]
    exact mdifferentiableAt_extChartAt (by simp)
  have hcomp :=
    mfderiv_comp_apply_of_eq (1 : GL (Fin n) ℝ) hgramDiff hvalDiff (by rfl) A
  rw [realGeneralLinearGroup_val_mfderiv_eq_id] at hcomp
  have hambient :=
    congrArg (fun L : Mℝ(n) →L[ℝ] Mℝ(n) ↦ L A) hgram.mfderiv
  calc
    mfderiv (Iℝ(n)) (Iℝ(n))
        (fun g : GL (Fin n) ℝ ↦ (g : Mℝ(n)).transpose * (g : Mℝ(n))) 1 A =
        mfderiv (Iℝ(n)) (Iℝ(n)) (fun B : Mℝ(n) ↦ B.transpose * B) 1 A := by
      simpa [Function.comp_def] using! hcomp
    _ = realMatrixGramRawDerivAtOne n A := by
      simpa using! hambient
    _ = A.transpose + A := realMatrixGramRawDerivAtOne_apply n A

/-- The Gram-map differential on the underlying real complex general linear group is conjugate
transpose plus identity. -/
private theorem realComplexGeneralLinearGroup_gram_mfderiv_one_apply
    (n : ℕ) (A : Mℂ(n)) :
    mfderiv (Iℝℂ(n)) (Iℝℂ(n))
      (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))ᴴ * (g : Mℂ(n))) 1 A =
        Aᴴ + A := by
  have hgram := (complexMatrixGram_hasFDerivAt_one n).hasMFDerivAt
  have hgramDiff :
      MDifferentiableAt (Iℝℂ(n)) (Iℝℂ(n))
        (fun B : Mℂ(n) ↦ Bᴴ * B) 1 :=
    hgram.mdifferentiableAt
  have hvalDiff :
      MDifferentiableAt (Iℝℂ(n)) (Iℝℂ(n))
        (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) 1 := by
    have hchart :
        (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) =
          extChartAt (Iℝℂ(n)) (1 : GL (Fin n) ℂ) := by
      funext g
      rfl
    rw [hchart]
    exact mdifferentiableAt_extChartAt (by simp)
  have hcomp :=
    mfderiv_comp_apply_of_eq (1 : GL (Fin n) ℂ) hgramDiff hvalDiff (by rfl) A
  rw [realComplexGeneralLinearGroup_val_mfderiv_eq_id] at hcomp
  have hambient :=
    congrArg (fun L : Mℂ(n) →L[ℝ] Mℂ(n) ↦ L A) hgram.mfderiv
  calc
    mfderiv (Iℝℂ(n)) (Iℝℂ(n))
        (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))ᴴ * (g : Mℂ(n))) 1 A =
        mfderiv (Iℝℂ(n)) (Iℝℂ(n)) (fun B : Mℂ(n) ↦ Bᴴ * B) 1 A := by
      simpa [Function.comp_def] using! hcomp
    _ = complexMatrixGramRawDerivAtOne n A := by
      simpa using! hambient
    _ = Aᴴ + A := complexMatrixGramRawDerivAtOne_apply n A

/- The next lemmas identify the intrinsic bracket on the units of an arbitrary complete normed
algebra with its associative commutator.  They are the normed-algebra form of the calculation for
general linear groups in Proposition 8.41. -/

private theorem unitsVal_mfderiv_eq_id
    {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]
    (g : Rˣ) :
    mfderiv (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R) (fun h : Rˣ ↦ (h : R)) g =
      ContinuousLinearMap.id 𝕜 R := by
  have hchart :
      extChartAt (modelWithCornersSelf 𝕜 R) g = fun h : Rˣ ↦ (h : R) := by
    funext h
    rfl
  rw [← hchart]
  simpa using! (mfderiv_extChartAt_self (I := modelWithCornersSelf 𝕜 R) (x := g))

private theorem units_leftMulToAmbient_hasMFDerivAt
    {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]
    (g : Rˣ) :
    HasMFDerivAt (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R)
      (fun h : Rˣ ↦ (g : R) * (h : R)) 1
      ((g : R) • ContinuousLinearMap.id 𝕜 R) := by
  have hconst :
      HasMFDerivAt (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R)
        (fun _ : Rˣ ↦ (g : R)) 1
        (0 : GroupLieAlgebra (modelWithCornersSelf 𝕜 R) Rˣ →L[𝕜] R) := by
    simpa using
      (show HasMFDerivAt (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R)
          (fun _ : Rˣ ↦ (g : R)) 1
          (0 : GroupLieAlgebra (modelWithCornersSelf 𝕜 R) Rˣ →L[𝕜] R) from
        hasMFDerivAt_const (c := (g : R)) (x := (1 : Rˣ)))
  have hvalDiff :
      MDifferentiableAt (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R)
        (fun h : Rˣ ↦ (h : R)) 1 := by
    rw [show (fun h : Rˣ ↦ (h : R)) = extChartAt (modelWithCornersSelf 𝕜 R) (1 : Rˣ) by
      funext h
      rfl]
    exact mdifferentiableAt_extChartAt (by simp)
  have hval :
      HasMFDerivAt (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R)
        (fun h : Rˣ ↦ (h : R)) 1 (ContinuousLinearMap.id 𝕜 R) :=
    hvalDiff.hasMFDerivAt.congr_mfderiv (unitsVal_mfderiv_eq_id (g := (1 : Rˣ)))
  have hmul := hconst.mul' hval
  have hderiv :
      ((g : R) • ContinuousLinearMap.id 𝕜 R +
          MulOpposite.op (1 : R) • (0 : R →L[𝕜] R)) =
        ((g : R) • ContinuousLinearMap.id 𝕜 R) := by
    ext v
    simp [ContinuousLinearMap.smul_apply]
  exact hmul.congr_mfderiv hderiv

private theorem units_mulInvariantVectorField_apply
    {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]
    (A : GroupLieAlgebra (modelWithCornersSelf 𝕜 R) Rˣ) (g : Rˣ) :
    mulInvariantVectorField A g = (g : R) * (show R from A) := by
  let valMap : Rˣ → R := fun h ↦ (h : R)
  have hmin : minSmoothness 𝕜 3 ≠ 0 :=
    lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hValAtg : MDifferentiableAt (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R) valMap g := by
    rw [show valMap = extChartAt (modelWithCornersSelf 𝕜 R) g by
      funext h
      rfl]
    exact mdifferentiableAt_extChartAt (by simp)
  have hLeft : MDifferentiableAt (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R) (g * ·) (1 : Rˣ) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hmin
  have hcomp :
      mfderiv (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R) valMap g (mulInvariantVectorField A g) =
        mfderiv (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R) (valMap ∘ (g * ·)) 1 A := by
    simpa [valMap, mulInvariantVectorField] using
      (mfderiv_comp_apply_of_eq (1 : Rˣ) hValAtg hLeft (mul_one g) A).symm
  have hambient :
      mfderiv (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R) (valMap ∘ (g * ·)) 1 A =
        (g : R) * (show R from A) := by
    have hEq : valMap ∘ (g * ·) = fun h : Rˣ ↦ (g : R) * (h : R) := by
      funext h
      rfl
    rw [hEq]
    have h := congrArg (fun f : GroupLieAlgebra (modelWithCornersSelf 𝕜 R) Rˣ →L[𝕜] R ↦ f A)
      (units_leftMulToAmbient_hasMFDerivAt (g := g)).mfderiv
    exact h
  rw [unitsVal_mfderiv_eq_id (g := g)] at hcomp
  exact hcomp.trans hambient

private theorem unitsAmbientPullback_mulField
    {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]
    (A : R) :
    VectorField.mpullback (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R)
      (fun g : Rˣ ↦ (g : R))
      (fun X : R ↦ X * A) = fun g : Rˣ ↦ (g : R) * A := by
  have hInv : (ContinuousLinearMap.id 𝕜 R).inverse = ContinuousLinearMap.id 𝕜 R := by
    simp
  funext g
  rw [VectorField.mpullback_apply, unitsVal_mfderiv_eq_id (g := g), hInv]
  rfl

private theorem unitsBracketAtOne_eq_ambientLieBracket
    {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]
    (A B : R) :
    VectorField.mlieBracket (modelWithCornersSelf 𝕜 R)
      (fun g : Rˣ ↦ (g : R) * A) (fun g : Rˣ ↦ (g : R) * B) 1 =
      VectorField.lieBracket 𝕜 (fun X : R ↦ X * A) (fun X : R ↦ X * B) 1 := by
  have hInv : (ContinuousLinearMap.id 𝕜 R).inverse = ContinuousLinearMap.id 𝕜 R := by
    simp
  have hA :=
    ((contMDiffAt_vectorSpace_iff_contDiffAt (V := fun X : R ↦ X * A) (x := (1 : R))).2
      (((ContinuousLinearMap.mul 𝕜 R).flip A).contDiff (n := 1)).contDiffAt).mdifferentiableAt
        one_ne_zero
  have hB :=
    ((contMDiffAt_vectorSpace_iff_contDiffAt (V := fun X : R ↦ X * B) (x := (1 : R))).2
      (((ContinuousLinearMap.mul 𝕜 R).flip B).contDiff (n := 1)).contDiffAt).mdifferentiableAt
        one_ne_zero
  have hval :
      ContMDiffAt (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R) (minSmoothness 𝕜 2)
        (fun g : Rˣ ↦ (g : R)) 1 := by
    simpa using
      (Units.contMDiff_val (𝕜 := 𝕜) (R := R) (n := minSmoothness 𝕜 2)).contMDiffAt
  have hpull :
      VectorField.mpullback (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R)
          (fun g : Rˣ ↦ (g : R))
          (VectorField.mlieBracket (modelWithCornersSelf 𝕜 R)
            (fun X : R ↦ X * A) (fun X : R ↦ X * B)) (1 : Rˣ) =
        VectorField.mlieBracket (modelWithCornersSelf 𝕜 R)
          (VectorField.mpullback (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R)
            (fun g : Rˣ ↦ (g : R)) (fun X : R ↦ X * A))
          (VectorField.mpullback (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 R)
            (fun g : Rˣ ↦ (g : R)) (fun X : R ↦ X * B)) (1 : Rˣ) := by
    exact VectorField.mpullback_mlieBracket hA hB hval le_rfl
  rw [VectorField.mpullback_apply, unitsAmbientPullback_mulField (A := A),
    unitsAmbientPullback_mulField (A := B), unitsVal_mfderiv_eq_id (g := (1 : Rˣ)),
    ← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin_univ] at hpull
  calc
    VectorField.mlieBracket (modelWithCornersSelf 𝕜 R)
        (fun g : Rˣ ↦ (g : R) * A) (fun g : Rˣ ↦ (g : R) * B) 1 =
        (ContinuousLinearMap.id 𝕜 R).inverse
          (VectorField.lieBracket 𝕜 (fun X : R ↦ X * A) (fun X : R ↦ X * B) 1) :=
      hpull.symm
    _ = VectorField.lieBracket 𝕜 (fun X : R ↦ X * A) (fun X : R ↦ X * B) 1 := by
      rw [hInv]
      rfl

private theorem unitsAmbientLieBracket_apply
    {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]
    (A B X : R) :
    VectorField.lieBracket 𝕜 (fun Y : R ↦ Y * A) (fun Y : R ↦ Y * B) X =
      X * (A * B - B * A) := by
  have hBderiv :=
    fderiv_mul_const' (𝕜 := 𝕜) (a := fun Y : R ↦ Y) (x := X) differentiableAt_id B
  have hAderiv :=
    fderiv_mul_const' (𝕜 := 𝕜) (a := fun Y : R ↦ Y) (x := X) differentiableAt_id A
  have hId : fderiv 𝕜 (fun Y : R ↦ Y) X = ContinuousLinearMap.id 𝕜 R :=
    fderiv_id (x := X)
  rw [VectorField.lieBracket, hBderiv, hAderiv, hId]
  simpa [ContinuousLinearMap.smul_apply, mul_assoc] using (mul_sub X (A * B) (B * A)).symm

private theorem unitsGroupLieBracket_eq_commutator
    {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]
    (A B : GroupLieAlgebra (modelWithCornersSelf 𝕜 R) Rˣ) :
    ⁅A, B⁆ =
      (show GroupLieAlgebra (modelWithCornersSelf 𝕜 R) Rˣ from
        (show R from A) * (show R from B) - (show R from B) * (show R from A)) := by
  rw [GroupLieAlgebra.bracket_def]
  have hA : mulInvariantVectorField A = fun g : Rˣ ↦ (g : R) * (show R from A) := by
    funext g
    exact units_mulInvariantVectorField_apply A g
  have hB : mulInvariantVectorField B = fun g : Rˣ ↦ (g : R) * (show R from B) := by
    funext g
    exact units_mulInvariantVectorField_apply B g
  rw [hA, hB, unitsBracketAtOne_eq_ambientLieBracket]
  simpa using unitsAmbientLieBracket_apply (show R from A) (show R from B) (1 : R)

/-- The tangent-space carrier of the real matrix general linear group is linearly the ambient
matrix space. -/
private noncomputable def realGLGroupLieAlgebraEquivMatrix (n : ℕ) :
    GroupLieAlgebra (Iℝ(n)) (GL (Fin n) ℝ) ≃ₗ[ℝ] Mℝ(n) where
  toFun := fun A ↦ A
  invFun := fun A ↦ A
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := fun A ↦ rfl
  right_inv := fun A ↦ rfl

/-- The complex-linear tangent-space carrier of the complex matrix general linear group is the
ambient complex matrix space. -/
private noncomputable def complexGLGroupLieAlgebraEquivMatrix (n : ℕ) :
    GroupLieAlgebra (Iℂ(n)) (GL (Fin n) ℂ) ≃ₗ[ℂ] Mℂ(n) where
  toFun := fun A ↦ A
  invFun := fun A ↦ A
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := fun A ↦ rfl
  right_inv := fun A ↦ rfl

/-- The real tangent-space carrier of the complex matrix general linear group is the underlying
real matrix space. -/
private noncomputable def realComplexGLGroupLieAlgebraEquivMatrix (n : ℕ) :
    GroupLieAlgebra (Iℝℂ(n)) (GL (Fin n) ℂ) ≃ₗ[ℝ] Mℂ(n) where
  toFun := fun A ↦ A
  invFun := fun A ↦ A
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := fun A ↦ rfl
  right_inv := fun A ↦ rfl

/-- After transporting the subgroup tangent image to a fixed finite-dimensional model, an
inclusion of submodules is equality when their dimensions agree. -/
private theorem mappedGroupLieSubalgebra_eq_of_le_of_finrank_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (⊤ : WithTop ℕ∞) G]
    (S : @LieSubgroup 𝕜 _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (e : GroupLieAlgebra I G ≃ₗ[𝕜] V)
    (L : Submodule 𝕜 V)
    (hle :
      (LieSubgroup.groupLieSubalgebra S).toSubmodule.map e.toLinearMap ≤ L)
    (hdim : Module.finrank 𝕜 S.ModelSpace = Module.finrank 𝕜 L) :
    (LieSubgroup.groupLieSubalgebra S).toSubmodule.map e.toLinearMap = L := by
  haveI : FiniteDimensional 𝕜 S.ModelSpace :=
    LieSubgroup.finiteDimensionalModelSpace S
  have hsubgroupDim :
      Module.finrank 𝕜 (LieSubgroup.groupLieSubalgebra S) =
        Module.finrank 𝕜 S.ModelSpace := by
    simpa [GroupLieAlgebra, TangentSpace] using
      (LieSubgroup.groupLieSubalgebraEquiv S).toLinearEquiv.finrank_eq.symm
  have hmapDim' :
      Module.finrank 𝕜
          ((LieSubgroup.groupLieSubalgebra S).toSubmodule.map e.toLinearMap) =
        Module.finrank 𝕜 (LieSubgroup.groupLieSubalgebra S).toSubmodule :=
    (e.submoduleMap (LieSubgroup.groupLieSubalgebra S).toSubmodule).finrank_eq.symm
  have hsame :
      Module.finrank 𝕜 (LieSubgroup.groupLieSubalgebra S).toSubmodule =
        Module.finrank 𝕜 (LieSubgroup.groupLieSubalgebra S) := by
    rfl
  have hmapDim :
      Module.finrank 𝕜
          ((LieSubgroup.groupLieSubalgebra S).toSubmodule.map e.toLinearMap) =
        Module.finrank 𝕜 (LieSubgroup.groupLieSubalgebra S) :=
    hmapDim'.trans hsame
  have hfin :
      Module.finrank 𝕜
          ((LieSubgroup.groupLieSubalgebra S).toSubmodule.map e.toLinearMap) =
        Module.finrank 𝕜 L :=
    hmapDim.trans (hsubgroupDim.trans hdim)
  exact Submodule.eq_of_le_of_finrank_eq hle hfin

/-- Membership is transported by an equality between the mapped subgroup tangent image and a
fixed linear subspace. -/
private theorem mem_groupLieSubalgebra_iff_equiv_mem
    {𝕜 : Type*} [Semiring 𝕜]
    {V W : Type*} [AddCommMonoid V] [Module 𝕜 V]
    [AddCommMonoid W] [Module 𝕜 W]
    (K : Submodule 𝕜 V) (e : V ≃ₗ[𝕜] W) (L : Submodule 𝕜 W)
    (heq : K.map e.toLinearMap = L) (A : V) :
    A ∈ K ↔ e A ∈ L := by
  constructor
  · intro hA
    have hmap : e A ∈ K.map e.toLinearMap :=
      Submodule.mem_map_of_mem hA
    rwa [heq] at hmap
  · intro hA
    have hmap : e A ∈ K.map e.toLinearMap := by
      rwa [heq]
    rcases hmap with ⟨Y, hY, hYA⟩
    have : Y = A := e.injective hYA
    simpa [this] using hY

-- Semantic recall: Theorem 8.46 already exposes the canonical ambient Lie-subalgebra owner as
-- `LieSubgroup.groupLieSubalgebra` with equivalence `LieSubgroup.groupLieSubalgebraEquiv`; the
-- matrix-side targets are mathlib's `sl`/`so` and the local `u`/`su` matrix Lie subalgebras.

/-- Auxiliary membership characterization for the Lie subalgebra of a `GL(n, ℝ)` Lie subgroup
whose carrier is the canonical copy of `SL(n, ℝ)`. -/
private theorem special_linear_real_groupLieSubalgebra_eq_sl
    (n : ℕ)
    (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearRealSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.SpecialLinear.sl (Fin n) ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ LieSubgroup.groupLieSubalgebra S ↔
      A ∈ LieAlgebra.SpecialLinear.sl (Fin n) ℝ := by
  let detGL : GL (Fin n) ℝ → ℝ :=
    fun g ↦ Matrix.det (g : Mℝ(n))
  have hdetDiff :
      MDifferentiableAt (Iℝ(n)) (𝓘(ℝ)) detGL 1 := by
    have hambient :
        MDifferentiableAt (Iℝ(n)) (𝓘(ℝ))
          (Matrix.det : Mℝ(n) → ℝ) 1 :=
      (matrixDet_hasFDerivAt_one (R := ℝ) n).hasMFDerivAt.mdifferentiableAt
    have hval :
        MDifferentiableAt (Iℝ(n)) (Iℝ(n))
          (fun g : GL (Fin n) ℝ ↦ (g : Mℝ(n))) 1 := by
      have hchart :
          (fun g : GL (Fin n) ℝ ↦ (g : Mℝ(n))) =
            extChartAt (Iℝ(n)) (1 : GL (Fin n) ℝ) := by
        funext g
        rfl
      rw [hchart]
      exact mdifferentiableAt_extChartAt (by simp)
    exact hambient.comp (1 : GL (Fin n) ℝ) hval
  have hconst : ∀ x : S.carrier, detGL x.1 = detGL 1 := by
    intro x
    have hx : x.1 ∈ specialLinearRealSubgroupInGeneralLinearGroup n := by
      rw [← hS]
      exact x.2
    rw [specialLinearRealSubgroupInGeneralLinearGroup_eq_det_ker] at hx
    have hxdet :
        Matrix.GeneralLinearGroup.det x.1 = 1 :=
      (MonoidHom.mem_ker.mp hx)
    simpa [detGL] using congrArg Units.val hxdet
  have hle :
      (LieSubgroup.groupLieSubalgebra S).toSubmodule.map
          (realGLGroupLieAlgebraEquivMatrix n).toLinearMap ≤
        (LieAlgebra.SpecialLinear.sl (Fin n) ℝ).toSubmodule := by
    rintro X ⟨Y, hY, rfl⟩
    change Matrix.trace (realGLGroupLieAlgebraEquivMatrix n Y) = 0
    have hz :=
      mfderiv_eq_zero_on_groupLieSubalgebra S detGL hdetDiff hconst hY
    change
      mfderiv (Iℝ(n)) (modelWithCornersSelf ℝ ℝ)
        (fun g : GL (Fin n) ℝ ↦ Matrix.det (g : Mℝ(n))) 1 Y = 0 at hz
    rw [realGeneralLinearGroup_det_mfderiv_one_apply] at hz
    exact hz
  have heq :
      (LieSubgroup.groupLieSubalgebra S).toSubmodule.map
          (realGLGroupLieAlgebraEquivMatrix n).toLinearMap =
        (LieAlgebra.SpecialLinear.sl (Fin n) ℝ).toSubmodule :=
    mappedGroupLieSubalgebra_eq_of_le_of_finrank_eq S
      (realGLGroupLieAlgebraEquivMatrix n)
      (LieAlgebra.SpecialLinear.sl (Fin n) ℝ).toSubmodule hle hdim
  simpa [realGLGroupLieAlgebraEquivMatrix] using
    mem_groupLieSubalgebra_iff_equiv_mem
      (LieSubgroup.groupLieSubalgebra S).toSubmodule
      (realGLGroupLieAlgebraEquivMatrix n)
      (LieAlgebra.SpecialLinear.sl (Fin n) ℝ).toSubmodule heq
      (show GroupLieAlgebra (Iℝ(n)) (GL (Fin n) ℝ) from A)

/-- The Lie subalgebra attached to a `GL(n, ℝ)` realization of `SL(n, ℝ)` with the canonical
carrier is canonically identified with `𝔰𝔩(n, ℝ)` by the identity map on the underlying
matrices. -/
private noncomputable def special_linear_real_groupLieSubalgebraEquivSl
    (n : ℕ)
    (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearRealSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.SpecialLinear.sl (Fin n) ℝ)) :
    LieSubgroup.groupLieSubalgebra S ≃ₗ⁅ℝ⁆
      LieAlgebra.SpecialLinear.sl (Fin n) ℝ where
  toFun := fun A ↦
    ⟨A.1, (special_linear_real_groupLieSubalgebra_eq_sl n S hS hdim A.1).1 A.2⟩
  invFun := fun A ↦
    ⟨A.1, (special_linear_real_groupLieSubalgebra_eq_sl n S hS hdim A.1).2 A.2⟩
  map_add' := by
    intro A B
    rfl
  map_smul' := by
    intro c A
    rfl
  map_lie' := by
    intro A B
    apply Subtype.ext
    simpa [matrixLieBracket_eq_commutator] using
      congrArg
        (fun X : GroupLieAlgebra (Iℝ(n)) (GL (Fin n) ℝ) ↦ (show Mℝ(n) from X))
        (unitsGroupLieBracket_eq_commutator A.1 B.1)
  left_inv := by
    intro A
    rfl
  right_inv := by
    intro A
    rfl

/-- Helper for Problem 8-29: if `S` is a Lie subgroup of `GL(n, ℝ)` whose carrier is the
canonical copy of `SL(n, ℝ)`, then its Lie algebra is canonically isomorphic to `𝔰𝔩(n, ℝ)`. -/
private noncomputable def special_linear_real_group_lie_isomorphic_to_sl
    (n : ℕ)
    (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearRealSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.SpecialLinear.sl (Fin n) ℝ)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier ≃ₗ⁅ℝ⁆
      LieAlgebra.SpecialLinear.sl (Fin n) ℝ := by
  exact
    (LieSubgroup.groupLieSubalgebraEquiv S).trans
      (special_linear_real_groupLieSubalgebraEquivSl n S hS hdim)

/-- After identifying the ambient image with `𝔰𝔩(n, ℝ)`, the canonical equivalence agrees with
the inclusion into the ambient matrix Lie algebra. -/
private theorem special_linear_real_group_lie_isomorphic_to_sl_def
    (n : ℕ)
    (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearRealSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.SpecialLinear.sl (Fin n) ℝ))
    (X : GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier) :
    (special_linear_real_group_lie_isomorphic_to_sl n S hS hdim X).1 =
      (LieSubgroup.groupLieSubalgebraEquiv S X).1 := by
  -- The second equivalence is the identity on the underlying ambient matrix.
  rfl

/-- Auxiliary membership characterization for the Lie subalgebra of a `GL(n, ℝ)` Lie subgroup
whose carrier is the canonical copy of `SO(n)`. -/
private theorem special_orthogonal_groupLieSubalgebra_eq_so
    (n : ℕ)
    (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialOrthogonalSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.Orthogonal.so (Fin n) ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ LieSubgroup.groupLieSubalgebra S ↔
      A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  let gramGL : GL (Fin n) ℝ → Mℝ(n) :=
    fun g ↦ (g : Mℝ(n)).transpose * (g : Mℝ(n))
  have hgramDiff : MDifferentiableAt (Iℝ(n)) (Iℝ(n)) gramGL 1 := by
    have hambient :
        MDifferentiableAt (Iℝ(n)) (Iℝ(n))
          (fun B : Mℝ(n) ↦ B.transpose * B) 1 :=
      (realMatrixGram_hasFDerivAt_one n).hasMFDerivAt.mdifferentiableAt
    have hval :
        MDifferentiableAt (Iℝ(n)) (Iℝ(n))
          (fun g : GL (Fin n) ℝ ↦ (g : Mℝ(n))) 1 := by
      have hchart :
          (fun g : GL (Fin n) ℝ ↦ (g : Mℝ(n))) =
            extChartAt (Iℝ(n)) (1 : GL (Fin n) ℝ) := by
        funext g
        rfl
      rw [hchart]
      exact mdifferentiableAt_extChartAt (by simp)
    exact hambient.comp (1 : GL (Fin n) ℝ) hval
  have hconst : ∀ x : S.carrier, gramGL x.1 = gramGL 1 := by
    intro x
    have hx : x.1 ∈ specialOrthogonalSubgroupInGeneralLinearGroup n := by
      rw [← hS]
      exact x.2
    have hxSO :=
      (mem_specialOrthogonalSubgroupInGeneralLinearGroup_iff n x.1).1 hx
    have hgram :=
      (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1
        ((Matrix.mem_specialOrthogonalGroup_iff).1 hxSO).1
    simpa [gramGL] using hgram
  have hle :
      (LieSubgroup.groupLieSubalgebra S).toSubmodule.map
          (realGLGroupLieAlgebraEquivMatrix n).toLinearMap ≤
        (LieAlgebra.Orthogonal.so (Fin n) ℝ).toSubmodule := by
    rintro X ⟨Y, hY, rfl⟩
    change realGLGroupLieAlgebraEquivMatrix n Y ∈
      LieAlgebra.Orthogonal.so (Fin n) ℝ
    rw [mem_orthogonalLieSubalgebra_iff_transpose_add_eq_zero]
    change
      (realGLGroupLieAlgebraEquivMatrix n Y).transpose +
          realGLGroupLieAlgebraEquivMatrix n Y = 0
    have hz :=
      mfderiv_eq_zero_on_groupLieSubalgebra S gramGL hgramDiff hconst hY
    change
      mfderiv (Iℝ(n)) (Iℝ(n))
        (fun g : GL (Fin n) ℝ ↦
          (g : Mℝ(n)).transpose * (g : Mℝ(n))) 1 Y = 0 at hz
    rw [realGeneralLinearGroup_gram_mfderiv_one_apply] at hz
    exact hz
  have heq :
      (LieSubgroup.groupLieSubalgebra S).toSubmodule.map
          (realGLGroupLieAlgebraEquivMatrix n).toLinearMap =
        (LieAlgebra.Orthogonal.so (Fin n) ℝ).toSubmodule :=
    mappedGroupLieSubalgebra_eq_of_le_of_finrank_eq S
      (realGLGroupLieAlgebraEquivMatrix n)
      (LieAlgebra.Orthogonal.so (Fin n) ℝ).toSubmodule hle hdim
  simpa [realGLGroupLieAlgebraEquivMatrix] using
    mem_groupLieSubalgebra_iff_equiv_mem
      (LieSubgroup.groupLieSubalgebra S).toSubmodule
      (realGLGroupLieAlgebraEquivMatrix n)
      (LieAlgebra.Orthogonal.so (Fin n) ℝ).toSubmodule heq
      (show GroupLieAlgebra (Iℝ(n)) (GL (Fin n) ℝ) from A)

/-- The Lie subalgebra attached to a `GL(n, ℝ)` realization of `SO(n)` with the canonical carrier
is canonically identified with `𝔬(n)` by the identity map on the underlying matrices. -/
private noncomputable def special_orthogonal_groupLieSubalgebraEquivSo
    (n : ℕ)
    (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialOrthogonalSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.Orthogonal.so (Fin n) ℝ)) :
    LieSubgroup.groupLieSubalgebra S ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ where
  toFun := fun A ↦
    ⟨A.1, (special_orthogonal_groupLieSubalgebra_eq_so n S hS hdim A.1).1 A.2⟩
  invFun := fun A ↦
    ⟨A.1, (special_orthogonal_groupLieSubalgebra_eq_so n S hS hdim A.1).2 A.2⟩
  map_add' := by
    intro A B
    rfl
  map_smul' := by
    intro c A
    rfl
  map_lie' := by
    intro A B
    apply Subtype.ext
    simpa [matrixLieBracket_eq_commutator] using
      congrArg
        (fun X : GroupLieAlgebra (Iℝ(n)) (GL (Fin n) ℝ) ↦ (show Mℝ(n) from X))
        (unitsGroupLieBracket_eq_commutator A.1 B.1)
  left_inv := by
    intro A
    rfl
  right_inv := by
    intro A
    rfl

/-- Helper for Problem 8-29: if `S` is a Lie subgroup of `GL(n, ℝ)` whose carrier is the
canonical copy of `SO(n)`, then its Lie algebra is canonically isomorphic to `𝔬(n)`. -/
private noncomputable def special_orthogonal_group_lie_isomorphic_to_so
    (n : ℕ)
    (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialOrthogonalSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.Orthogonal.so (Fin n) ℝ)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  exact
    (LieSubgroup.groupLieSubalgebraEquiv S).trans
      (special_orthogonal_groupLieSubalgebraEquivSo n S hS hdim)

/-- After identifying the ambient image with `𝔬(n)`, the canonical equivalence agrees with the
inclusion into the ambient matrix Lie algebra. -/
private theorem special_orthogonal_group_lie_isomorphic_to_so_def
    (n : ℕ)
    (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialOrthogonalSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.Orthogonal.so (Fin n) ℝ))
    (X : GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier) :
    (special_orthogonal_group_lie_isomorphic_to_so n S hS hdim X).1 =
      (LieSubgroup.groupLieSubalgebraEquiv S X).1 := by
  -- The second equivalence is the identity on the underlying ambient matrix.
  rfl

/-- Auxiliary membership characterization for the Lie subalgebra of a `GL(n, ℂ)` Lie subgroup
whose carrier is the canonical copy of `SL(n, ℂ)`. -/
private theorem special_linear_complex_groupLieSubalgebra_eq_sl
    (n : ℕ)
    (S : ComplexLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearComplexSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℂ S.ModelSpace =
        Module.finrank ℂ (LieAlgebra.SpecialLinear.sl (Fin n) ℂ))
    (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ LieSubgroup.groupLieSubalgebra S ↔
      A ∈ LieAlgebra.SpecialLinear.sl (Fin n) ℂ := by
  let detGL : GL (Fin n) ℂ → ℂ :=
    fun g ↦ Matrix.det (g : Mℂ(n))
  have hdetDiff :
      MDifferentiableAt (Iℂ(n)) (modelWithCornersSelf ℂ ℂ) detGL 1 := by
    have hambient :
        MDifferentiableAt (Iℂ(n)) (modelWithCornersSelf ℂ ℂ)
          (Matrix.det : Mℂ(n) → ℂ) 1 :=
      (matrixDet_hasFDerivAt_one (R := ℂ) n).hasMFDerivAt.mdifferentiableAt
    have hval :
        MDifferentiableAt (Iℂ(n)) (Iℂ(n))
          (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) 1 := by
      have hchart :
          (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) =
            extChartAt (Iℂ(n)) (1 : GL (Fin n) ℂ) := by
        funext g
        rfl
      rw [hchart]
      exact mdifferentiableAt_extChartAt (by simp)
    exact hambient.comp (1 : GL (Fin n) ℂ) hval
  have hconst : ∀ x : S.carrier, detGL x.1 = detGL 1 := by
    intro x
    have hx : x.1 ∈ specialLinearComplexSubgroupInGeneralLinearGroup n := by
      rw [← hS]
      exact x.2
    rw [specialLinearComplexSubgroupInGeneralLinearGroup_eq_det_ker] at hx
    have hxdet : Matrix.GeneralLinearGroup.det x.1 = 1 :=
      MonoidHom.mem_ker.mp hx
    simpa [detGL] using congrArg Units.val hxdet
  have hle :
      (LieSubgroup.groupLieSubalgebra S).toSubmodule.map
          (complexGLGroupLieAlgebraEquivMatrix n).toLinearMap ≤
        (LieAlgebra.SpecialLinear.sl (Fin n) ℂ).toSubmodule := by
    rintro X ⟨Y, hY, rfl⟩
    change Matrix.trace (complexGLGroupLieAlgebraEquivMatrix n Y) = 0
    have hz :=
      mfderiv_eq_zero_on_groupLieSubalgebra S detGL hdetDiff hconst hY
    change
      mfderiv (Iℂ(n)) (modelWithCornersSelf ℂ ℂ)
        (fun g : GL (Fin n) ℂ ↦ Matrix.det (g : Mℂ(n))) 1 Y = 0 at hz
    rw [complexGeneralLinearGroup_det_mfderiv_one_apply] at hz
    exact hz
  have heq :
      (LieSubgroup.groupLieSubalgebra S).toSubmodule.map
          (complexGLGroupLieAlgebraEquivMatrix n).toLinearMap =
        (LieAlgebra.SpecialLinear.sl (Fin n) ℂ).toSubmodule :=
    mappedGroupLieSubalgebra_eq_of_le_of_finrank_eq S
      (complexGLGroupLieAlgebraEquivMatrix n)
      (LieAlgebra.SpecialLinear.sl (Fin n) ℂ).toSubmodule hle hdim
  simpa [complexGLGroupLieAlgebraEquivMatrix] using
    mem_groupLieSubalgebra_iff_equiv_mem
      (LieSubgroup.groupLieSubalgebra S).toSubmodule
      (complexGLGroupLieAlgebraEquivMatrix n)
      (LieAlgebra.SpecialLinear.sl (Fin n) ℂ).toSubmodule heq
      (show GroupLieAlgebra (Iℂ(n)) (GL (Fin n) ℂ) from A)

/-- The Lie subalgebra attached to a `GL(n, ℂ)` realization of `SL(n, ℂ)` with the canonical
carrier is canonically identified with `𝔰𝔩(n, ℂ)` by the identity map on the underlying
matrices. -/
private noncomputable def special_linear_complex_groupLieSubalgebraEquivSl
    (n : ℕ)
    (S : ComplexLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearComplexSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℂ S.ModelSpace =
        Module.finrank ℂ (LieAlgebra.SpecialLinear.sl (Fin n) ℂ)) :
    LieSubgroup.groupLieSubalgebra S ≃ₗ⁅ℂ⁆
      LieAlgebra.SpecialLinear.sl (Fin n) ℂ where
  toFun := fun A ↦
    ⟨A.1, (special_linear_complex_groupLieSubalgebra_eq_sl n S hS hdim A.1).1 A.2⟩
  invFun := fun A ↦
    ⟨A.1, (special_linear_complex_groupLieSubalgebra_eq_sl n S hS hdim A.1).2 A.2⟩
  map_add' := by
    intro A B
    rfl
  map_smul' := by
    intro c A
    rfl
  map_lie' := by
    intro A B
    apply Subtype.ext
    simpa [matrixLieBracket_eq_commutator] using
      congrArg
        (fun X : GroupLieAlgebra (Iℂ(n)) (GL (Fin n) ℂ) ↦ (show Mℂ(n) from X))
        (unitsGroupLieBracket_eq_commutator A.1 B.1)
  left_inv := by
    intro A
    rfl
  right_inv := by
    intro A
    rfl

/-- Helper for Problem 8-29: if `S` is a Lie subgroup of `GL(n, ℂ)` whose carrier is the
canonical copy of `SL(n, ℂ)`, then its Lie algebra is canonically isomorphic to `𝔰𝔩(n, ℂ)`. -/
private noncomputable def special_linear_complex_group_lie_isomorphic_to_sl
    (n : ℕ)
    (S : ComplexLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearComplexSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℂ S.ModelSpace =
        Module.finrank ℂ (LieAlgebra.SpecialLinear.sl (Fin n) ℂ)) :
    GroupLieAlgebra (modelWithCornersSelf ℂ S.ModelSpace) S.carrier ≃ₗ⁅ℂ⁆
      LieAlgebra.SpecialLinear.sl (Fin n) ℂ := by
  exact
    (LieSubgroup.groupLieSubalgebraEquiv S).trans
      (special_linear_complex_groupLieSubalgebraEquivSl n S hS hdim)

/-- `special_linear_complex_group_lie_isomorphic_to_sl` is the canonical equivalence after
identifying the ambient image with `𝔰𝔩(n, ℂ)`. -/
private theorem special_linear_complex_group_lie_isomorphic_to_sl_def
    (n : ℕ)
    (S : ComplexLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearComplexSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℂ S.ModelSpace =
        Module.finrank ℂ (LieAlgebra.SpecialLinear.sl (Fin n) ℂ))
    (X : GroupLieAlgebra (modelWithCornersSelf ℂ S.ModelSpace) S.carrier) :
    (special_linear_complex_group_lie_isomorphic_to_sl n S hS hdim X).1 =
      (LieSubgroup.groupLieSubalgebraEquiv S X).1 :=
  by
  -- The second equivalence is the identity on the underlying ambient matrix.
  rfl

/-- Auxiliary membership characterization for the Lie subalgebra of a `GL(n, ℂ)` Lie subgroup
whose carrier is the canonical copy of `U(n)`. -/
private theorem unitary_group_groupLieSubalgebra_eq_u
    (n : ℕ)
    (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = unitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (unitary_matrix_lie_subalgebra n))
    (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ LieSubgroup.groupLieSubalgebra S ↔
      A ∈ unitary_matrix_lie_subalgebra n := by
  let gramGL : GL (Fin n) ℂ → Mℂ(n) :=
    fun g ↦ (g : Mℂ(n))ᴴ * (g : Mℂ(n))
  have hgramDiff : MDifferentiableAt (Iℝℂ(n)) (Iℝℂ(n)) gramGL 1 := by
    have hambient :
        MDifferentiableAt (Iℝℂ(n)) (Iℝℂ(n))
          (fun B : Mℂ(n) ↦ Bᴴ * B) 1 :=
      (complexMatrixGram_hasFDerivAt_one n).hasMFDerivAt.mdifferentiableAt
    have hval :
        MDifferentiableAt (Iℝℂ(n)) (Iℝℂ(n))
          (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) 1 := by
      have hchart :
          (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) =
            extChartAt (Iℝℂ(n)) (1 : GL (Fin n) ℂ) := by
        funext g
        rfl
      rw [hchart]
      exact mdifferentiableAt_extChartAt (by simp)
    exact hambient.comp (1 : GL (Fin n) ℂ) hval
  have hconst : ∀ x : S.carrier, gramGL x.1 = gramGL 1 := by
    intro x
    have hx : x.1 ∈ unitarySubgroupInGeneralLinearGroup n := by
      rw [← hS]
      exact x.2
    have hgram := (mem_unitarySubgroupInGeneralLinearGroup_iff n x.1).1 hx
    simpa [gramGL, Matrix.star_eq_conjTranspose] using hgram
  have hle :
      (LieSubgroup.groupLieSubalgebra S).toSubmodule.map
          (realComplexGLGroupLieAlgebraEquivMatrix n).toLinearMap ≤
        (unitary_matrix_lie_subalgebra n).toSubmodule := by
    rintro X ⟨Y, hY, rfl⟩
    change realComplexGLGroupLieAlgebraEquivMatrix n Y ∈
      unitary_matrix_lie_subalgebra n
    rw [unitary_matrix_lie_subalgebra_mem]
    change
      (realComplexGLGroupLieAlgebraEquivMatrix n Y)ᴴ =
        -(realComplexGLGroupLieAlgebraEquivMatrix n Y)
    have hz :=
      mfderiv_eq_zero_on_groupLieSubalgebra S gramGL hgramDiff hconst hY
    change
      mfderiv (Iℝℂ(n)) (Iℝℂ(n))
        (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))ᴴ * (g : Mℂ(n))) 1 Y = 0 at hz
    rw [realComplexGeneralLinearGroup_gram_mfderiv_one_apply] at hz
    exact eq_neg_of_add_eq_zero_left hz
  have heq :
      (LieSubgroup.groupLieSubalgebra S).toSubmodule.map
          (realComplexGLGroupLieAlgebraEquivMatrix n).toLinearMap =
        (unitary_matrix_lie_subalgebra n).toSubmodule :=
    mappedGroupLieSubalgebra_eq_of_le_of_finrank_eq S
      (realComplexGLGroupLieAlgebraEquivMatrix n)
      (unitary_matrix_lie_subalgebra n).toSubmodule hle hdim
  simpa [realComplexGLGroupLieAlgebraEquivMatrix] using
    mem_groupLieSubalgebra_iff_equiv_mem
      (LieSubgroup.groupLieSubalgebra S).toSubmodule
      (realComplexGLGroupLieAlgebraEquivMatrix n)
      (unitary_matrix_lie_subalgebra n).toSubmodule heq
      (show GroupLieAlgebra (Iℝℂ(n)) (GL (Fin n) ℂ) from A)

/-- The Lie subalgebra attached to a `GL(n, ℂ)` realization of `U(n)` with the canonical carrier
is canonically identified with `𝔲(n)` by the identity map on the underlying matrices. -/
private noncomputable def unitary_group_groupLieSubalgebraEquivU
    (n : ℕ)
    (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = unitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (unitary_matrix_lie_subalgebra n)) :
    LieSubgroup.groupLieSubalgebra S ≃ₗ⁅ℝ⁆
      unitary_matrix_lie_subalgebra n where
  toFun := fun A ↦
    ⟨A.1, (unitary_group_groupLieSubalgebra_eq_u n S hS hdim A.1).1 A.2⟩
  invFun := fun A ↦
    ⟨A.1, (unitary_group_groupLieSubalgebra_eq_u n S hS hdim A.1).2 A.2⟩
  map_add' := by
    intro A B
    rfl
  map_smul' := by
    intro c A
    rfl
  map_lie' := by
    intro A B
    apply Subtype.ext
    simpa [matrixLieBracket_eq_commutator] using
      congrArg
        (fun X : GroupLieAlgebra (Iℝℂ(n)) (GL (Fin n) ℂ) ↦ (show Mℂ(n) from X))
        (unitsGroupLieBracket_eq_commutator A.1 B.1)
  left_inv := by
    intro A
    rfl
  right_inv := by
    intro A
    rfl

/-- Helper for Problem 8-29: if `S` is a Lie subgroup of `GL(n, ℂ)` whose carrier is the
canonical copy of `U(n)`, then its Lie algebra is canonically isomorphic to `𝔲(n)`. -/
private noncomputable def unitary_group_lie_isomorphic_to_u
    (n : ℕ)
    (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = unitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (unitary_matrix_lie_subalgebra n)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier ≃ₗ⁅ℝ⁆
      unitary_matrix_lie_subalgebra n := by
  exact
    (LieSubgroup.groupLieSubalgebraEquiv S).trans
      (unitary_group_groupLieSubalgebraEquivU n S hS hdim)

/-- `unitary_group_lie_isomorphic_to_u` is the canonical equivalence after identifying the ambient
image with `𝔲(n)`. -/
private theorem unitary_group_lie_isomorphic_to_u_def
    (n : ℕ)
    (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = unitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (unitary_matrix_lie_subalgebra n))
    (X : GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier) :
    (unitary_group_lie_isomorphic_to_u n S hS hdim X).1 =
      (LieSubgroup.groupLieSubalgebraEquiv S X).1 := by
  rfl

/-- Membership in `special_unitary_matrix_lie_subalgebra n` means skew-Hermitian together with
trace zero, equivalently membership in `𝔲(n)` plus the trace-zero condition. -/
theorem special_unitary_matrix_lie_subalgebra_mem_iff_unitary_mem_and_trace_eq_zero
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ special_unitary_matrix_lie_subalgebra n ↔
      A ∈ unitary_matrix_lie_subalgebra n ∧ Matrix.trace A = 0 := by
  -- Unpack both carrier predicates and compare the two equivalent conjunction presentations.
  simp [special_unitary_matrix_lie_subalgebra_mem, unitary_matrix_lie_subalgebra_mem]

/-- Helper for Problem 8-29: membership in `𝔰𝔲(n)` is equivalently membership in `𝔲(n)` together
with membership in `𝔰𝔩(n, ℂ)`. -/
theorem special_unitary_matrix_lie_subalgebra_mem_iff_unitary_mem_and_sl_mem
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ special_unitary_matrix_lie_subalgebra n ↔
      A ∈ unitary_matrix_lie_subalgebra n ∧
        A ∈ LieAlgebra.SpecialLinear.sl (Fin n) ℂ := by
  -- Normalize the trace-zero part using the `sl` membership characterization proved above.
  rw [special_unitary_matrix_lie_subalgebra_mem_iff_unitary_mem_and_trace_eq_zero,
    mem_specialLinearLieSubalgebra_iff_trace_eq_zero]

/-- Helper for Problem 8-29: a skew-Hermitian matrix has purely imaginary trace, so vanishing
imaginary part forces the trace itself to vanish. -/
private theorem trace_eq_zero_of_skewHermitian_of_im_eq_zero
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : Aᴴ = -A) (hIm : Complex.im (Matrix.trace A) = 0) :
    Matrix.trace A = 0 := by
  -- Taking traces turns the skew-Hermitian relation into `conj (trace A) = - trace A`.
  have hTraceStar : star (Matrix.trace A) = -Matrix.trace A := by
    simpa [Matrix.trace_conjTranspose] using congrArg Matrix.trace hA
  have hRe : Complex.re (Matrix.trace A) = 0 := by
    have hReEq : Complex.re (Matrix.trace A) = -Complex.re (Matrix.trace A) := by
      simpa using congrArg Complex.re hTraceStar
    linarith
  -- Vanishing real and imaginary parts forces the complex trace itself to vanish.
  apply Complex.ext <;> simp [hRe, hIm]

/-- Auxiliary membership characterization for the Lie subalgebra of a `GL(n, ℂ)` Lie subgroup
whose carrier is the canonical copy of `SU(n)`. -/
private theorem special_unitary_group_groupLieSubalgebra_eq_su
    (n : ℕ)
    (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialUnitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (special_unitary_matrix_lie_subalgebra n))
    (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ LieSubgroup.groupLieSubalgebra S ↔
      A ∈ special_unitary_matrix_lie_subalgebra n := by
  let gramGL : GL (Fin n) ℂ → Mℂ(n) :=
    fun g ↦ (g : Mℂ(n))ᴴ * (g : Mℂ(n))
  let detGL : GL (Fin n) ℂ → ℂ :=
    fun g ↦ Matrix.det (g : Mℂ(n))
  have hgramDiff : MDifferentiableAt (Iℝℂ(n)) (Iℝℂ(n)) gramGL 1 := by
    have hambient :
        MDifferentiableAt (Iℝℂ(n)) (Iℝℂ(n))
          (fun B : Mℂ(n) ↦ Bᴴ * B) 1 :=
      (complexMatrixGram_hasFDerivAt_one n).hasMFDerivAt.mdifferentiableAt
    have hval :
        MDifferentiableAt (Iℝℂ(n)) (Iℝℂ(n))
          (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) 1 := by
      have hchart :
          (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) =
            extChartAt (Iℝℂ(n)) (1 : GL (Fin n) ℂ) := by
        funext g
        rfl
      rw [hchart]
      exact mdifferentiableAt_extChartAt (by simp)
    exact hambient.comp (1 : GL (Fin n) ℂ) hval
  have hdetDiff :
      MDifferentiableAt (Iℝℂ(n)) (modelWithCornersSelf ℝ ℂ) detGL 1 := by
    have hambient :
        MDifferentiableAt (Iℝℂ(n)) (modelWithCornersSelf ℝ ℂ)
          (Matrix.det : Mℂ(n) → ℂ) 1 :=
      ((matrixDet_hasFDerivAt_one (R := ℂ) n).restrictScalars ℝ).hasMFDerivAt.mdifferentiableAt
    have hval :
        MDifferentiableAt (Iℝℂ(n)) (Iℝℂ(n))
          (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) 1 := by
      have hchart :
          (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))) =
            extChartAt (Iℝℂ(n)) (1 : GL (Fin n) ℂ) := by
        funext g
        rfl
      rw [hchart]
      exact mdifferentiableAt_extChartAt (by simp)
    exact hambient.comp (1 : GL (Fin n) ℂ) hval
  have hconstGram : ∀ x : S.carrier, gramGL x.1 = gramGL 1 := by
    intro x
    have hx : x.1 ∈ specialUnitarySubgroupInGeneralLinearGroup n := by
      rw [← hS]
      exact x.2
    have hxU :=
      (mem_specialUnitarySubgroupInGeneralLinearGroup_iff_mem_unitary_det_eq_one n x.1).1 hx |>.1
    have hgram := (mem_unitarySubgroupInGeneralLinearGroup_iff n x.1).1 hxU
    simpa [gramGL, Matrix.star_eq_conjTranspose] using hgram
  have hconstDet : ∀ x : S.carrier, detGL x.1 = detGL 1 := by
    intro x
    have hx : x.1 ∈ specialUnitarySubgroupInGeneralLinearGroup n := by
      rw [← hS]
      exact x.2
    have hxdet :=
      (mem_specialUnitarySubgroupInGeneralLinearGroup_iff_mem_unitary_det_eq_one n x.1).1 hx |>.2
    simpa [detGL] using congrArg Units.val hxdet
  have hle :
      (LieSubgroup.groupLieSubalgebra S).toSubmodule.map
          (realComplexGLGroupLieAlgebraEquivMatrix n).toLinearMap ≤
        (special_unitary_matrix_lie_subalgebra n).toSubmodule := by
    rintro X ⟨Y, hY, rfl⟩
    change realComplexGLGroupLieAlgebraEquivMatrix n Y ∈
      special_unitary_matrix_lie_subalgebra n
    rw [special_unitary_matrix_lie_subalgebra_mem]
    constructor
    · have hz :=
        mfderiv_eq_zero_on_groupLieSubalgebra S gramGL hgramDiff hconstGram hY
      change
        mfderiv (Iℝℂ(n)) (Iℝℂ(n))
          (fun g : GL (Fin n) ℂ ↦ (g : Mℂ(n))ᴴ * (g : Mℂ(n))) 1 Y = 0 at hz
      rw [realComplexGeneralLinearGroup_gram_mfderiv_one_apply] at hz
      exact eq_neg_of_add_eq_zero_left hz
    · have hz :=
        mfderiv_eq_zero_on_groupLieSubalgebra S detGL hdetDiff hconstDet hY
      change
        mfderiv (Iℝℂ(n)) (modelWithCornersSelf ℝ ℂ)
          (fun g : GL (Fin n) ℂ ↦ Matrix.det (g : Mℂ(n))) 1 Y = 0 at hz
      rw [realComplexGeneralLinearGroup_det_mfderiv_one_apply] at hz
      exact hz
  have heq :
      (LieSubgroup.groupLieSubalgebra S).toSubmodule.map
          (realComplexGLGroupLieAlgebraEquivMatrix n).toLinearMap =
        (special_unitary_matrix_lie_subalgebra n).toSubmodule :=
    mappedGroupLieSubalgebra_eq_of_le_of_finrank_eq S
      (realComplexGLGroupLieAlgebraEquivMatrix n)
      (special_unitary_matrix_lie_subalgebra n).toSubmodule hle hdim
  simpa [realComplexGLGroupLieAlgebraEquivMatrix] using
    mem_groupLieSubalgebra_iff_equiv_mem
      (LieSubgroup.groupLieSubalgebra S).toSubmodule
      (realComplexGLGroupLieAlgebraEquivMatrix n)
      (special_unitary_matrix_lie_subalgebra n).toSubmodule heq
      (show GroupLieAlgebra (Iℝℂ(n)) (GL (Fin n) ℂ) from A)

/-- The Lie subalgebra attached to a `GL(n, ℂ)` realization of `SU(n)` with the canonical carrier
is canonically identified with `𝔰𝔲(n)` by the identity map on the underlying matrices. -/
private noncomputable def special_unitary_group_groupLieSubalgebraEquivSu
    (n : ℕ)
    (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialUnitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (special_unitary_matrix_lie_subalgebra n)) :
    LieSubgroup.groupLieSubalgebra S ≃ₗ⁅ℝ⁆
      special_unitary_matrix_lie_subalgebra n where
  toFun := fun A ↦
    ⟨A.1, (special_unitary_group_groupLieSubalgebra_eq_su n S hS hdim A.1).1 A.2⟩
  invFun := fun A ↦
    ⟨A.1, (special_unitary_group_groupLieSubalgebra_eq_su n S hS hdim A.1).2 A.2⟩
  map_add' := by
    intro A B
    rfl
  map_smul' := by
    intro c A
    rfl
  map_lie' := by
    intro A B
    apply Subtype.ext
    simpa [matrixLieBracket_eq_commutator] using
      congrArg
        (fun X : GroupLieAlgebra (Iℝℂ(n)) (GL (Fin n) ℂ) ↦ (show Mℂ(n) from X))
        (unitsGroupLieBracket_eq_commutator A.1 B.1)
  left_inv := by
    intro A
    rfl
  right_inv := by
    intro A
    rfl

/-- Helper for Problem 8-29: if `S` is a Lie subgroup of `GL(n, ℂ)` whose carrier is the
canonical copy of `SU(n)`, then its Lie algebra is canonically isomorphic to `𝔰𝔲(n)`. -/
private noncomputable def special_unitary_group_lie_isomorphic_to_su
    (n : ℕ)
    (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialUnitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (special_unitary_matrix_lie_subalgebra n)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier ≃ₗ⁅ℝ⁆
      special_unitary_matrix_lie_subalgebra n := by
  exact
    (LieSubgroup.groupLieSubalgebraEquiv S).trans
      (special_unitary_group_groupLieSubalgebraEquivSu n S hS hdim)

/-- `special_unitary_group_lie_isomorphic_to_su` is the canonical equivalence after identifying
the ambient image with `𝔰𝔲(n)`. -/
private theorem special_unitary_group_lie_isomorphic_to_su_def
    (n : ℕ)
    (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialUnitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (special_unitary_matrix_lie_subalgebra n))
    (X : GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier) :
    (special_unitary_group_lie_isomorphic_to_su n S hS hdim X).1 =
      (LieSubgroup.groupLieSubalgebraEquiv S X).1 := by
  rfl

/-- The matrix Lie algebra `𝔰𝔲(n)` is the skew-Hermitian trace-zero Lie algebra, equivalently the
matrices belonging both to `𝔲(n)` and to `𝔰𝔩(n, ℂ)`. -/
theorem special_unitary_matrix_lie_subalgebra_mem_iff
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ special_unitary_matrix_lie_subalgebra n ↔
      A ∈ unitary_matrix_lie_subalgebra n ∧
        A ∈ LieAlgebra.SpecialLinear.sl (Fin n) ℂ :=
  special_unitary_matrix_lie_subalgebra_mem_iff_unitary_mem_and_sl_mem n A

/-- Problem 8-29 (1): for a Lie subgroup realization of `SL(n, ℝ)` in `GL(n, ℝ)`, Theorem 8.46
identifies its Lie algebra canonically with `𝔰𝔩(n, ℝ)`. -/
noncomputable def problem_8_29_special_linear_real
    (n : ℕ) (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearRealSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.SpecialLinear.sl (Fin n) ℝ)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier ≃ₗ⁅ℝ⁆
      LieAlgebra.SpecialLinear.sl (Fin n) ℝ :=
  special_linear_real_group_lie_isomorphic_to_sl n S hS hdim

/-- Under the canonical equivalence of Problem 8-29 (1), an element of `Lie(S)` is sent to the
same underlying matrix as under the ambient-image identification from Theorem 8.46. -/
theorem problem_8_29_special_linear_real_apply
    (n : ℕ) (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearRealSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.SpecialLinear.sl (Fin n) ℝ))
    (A : GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier) :
    (problem_8_29_special_linear_real n S hS hdim A).1 =
      (LieSubgroup.groupLieSubalgebraEquiv S A).1 :=
  special_linear_real_group_lie_isomorphic_to_sl_def n S hS hdim A

/-- Problem 8-29 (2): for a Lie subgroup realization of `SO(n)` in `GL(n, ℝ)`, Theorem 8.46
identifies its Lie algebra canonically with `𝔬(n)`. -/
noncomputable def problem_8_29_special_orthogonal
    (n : ℕ) (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialOrthogonalSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.Orthogonal.so (Fin n) ℝ)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ :=
  special_orthogonal_group_lie_isomorphic_to_so n S hS hdim

/-- Under the canonical equivalence of Problem 8-29 (2), an element of `Lie(S)` is sent to the
same underlying matrix as under the ambient-image identification from Theorem 8.46. -/
theorem problem_8_29_special_orthogonal_apply
    (n : ℕ) (S : RealLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialOrthogonalSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (LieAlgebra.Orthogonal.so (Fin n) ℝ))
    (A : GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier) :
    (problem_8_29_special_orthogonal n S hS hdim A).1 =
      (LieSubgroup.groupLieSubalgebraEquiv S A).1 :=
  special_orthogonal_group_lie_isomorphic_to_so_def n S hS hdim A

/-- Problem 8-29 (3): for a Lie subgroup realization of `SL(n, ℂ)` in `GL(n, ℂ)`, Theorem 8.46
identifies its Lie algebra canonically with `𝔰𝔩(n, ℂ)`. -/
noncomputable def problem_8_29_special_linear_complex
    (n : ℕ) (S : ComplexLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearComplexSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℂ S.ModelSpace =
        Module.finrank ℂ (LieAlgebra.SpecialLinear.sl (Fin n) ℂ)) :
    GroupLieAlgebra (modelWithCornersSelf ℂ S.ModelSpace) S.carrier ≃ₗ⁅ℂ⁆
      LieAlgebra.SpecialLinear.sl (Fin n) ℂ :=
  special_linear_complex_group_lie_isomorphic_to_sl n S hS hdim

/-- Under the canonical equivalence of Problem 8-29 (3), an element of `Lie(S)` is sent to the
same underlying matrix as under the ambient-image identification from Theorem 8.46. -/
theorem problem_8_29_special_linear_complex_apply
    (n : ℕ) (S : ComplexLieSubgroupGL(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearComplexSubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℂ S.ModelSpace =
        Module.finrank ℂ (LieAlgebra.SpecialLinear.sl (Fin n) ℂ))
    (A : GroupLieAlgebra (modelWithCornersSelf ℂ S.ModelSpace) S.carrier) :
    (problem_8_29_special_linear_complex n S hS hdim A).1 =
      (LieSubgroup.groupLieSubalgebraEquiv S A).1 :=
  special_linear_complex_group_lie_isomorphic_to_sl_def n S hS hdim A

/-- Problem 8-29 (4): for a Lie subgroup realization of `U(n)` in `GL(n, ℂ)`, Theorem 8.46
identifies its Lie algebra canonically with `𝔲(n)`. -/
noncomputable def problem_8_29_unitary
    (n : ℕ) (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = unitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (unitary_matrix_lie_subalgebra n)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier ≃ₗ⁅ℝ⁆
      unitary_matrix_lie_subalgebra n :=
  unitary_group_lie_isomorphic_to_u n S hS hdim

/-- Under the canonical equivalence of Problem 8-29 (4), an element of `Lie(S)` is sent to the
same underlying matrix as under the ambient-image identification from Theorem 8.46. -/
theorem problem_8_29_unitary_apply
    (n : ℕ) (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = unitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (unitary_matrix_lie_subalgebra n))
    (A : GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier) :
    (problem_8_29_unitary n S hS hdim A).1 =
      (LieSubgroup.groupLieSubalgebraEquiv S A).1 :=
  unitary_group_lie_isomorphic_to_u_def n S hS hdim A

/-- Problem 8-29 (5): for a Lie subgroup realization of `SU(n)` in `GL(n, ℂ)`, Theorem 8.46
identifies its Lie algebra canonically with `𝔰𝔲(n)`. -/
noncomputable def problem_8_29_special_unitary
    (n : ℕ) (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialUnitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (special_unitary_matrix_lie_subalgebra n)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier ≃ₗ⁅ℝ⁆
      special_unitary_matrix_lie_subalgebra n :=
  special_unitary_group_lie_isomorphic_to_su n S hS hdim

/-- Under the canonical equivalence of Problem 8-29 (5), an element of `Lie(S)` is sent to the
same underlying matrix as under the ambient-image identification from Theorem 8.46. -/
theorem problem_8_29_special_unitary_apply
    (n : ℕ) (S : RealLieSubgroupGLComplex(n)) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialUnitarySubgroupInGeneralLinearGroup n)
    (hdim :
      Module.finrank ℝ S.ModelSpace =
        Module.finrank ℝ (special_unitary_matrix_lie_subalgebra n))
    (A : GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier) :
    (problem_8_29_special_unitary n S hS hdim A).1 =
      (LieSubgroup.groupLieSubalgebraEquiv S A).1 :=
  special_unitary_group_lie_isomorphic_to_su_def n S hS hdim A
