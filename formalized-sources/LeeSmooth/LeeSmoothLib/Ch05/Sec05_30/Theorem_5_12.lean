import LeeSmoothLib.Verified.LevelSets.Generic
import Mathlib
import LeeSmoothLib.Ch04.Sec04_21.Exercise_4_4
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_2
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section ConstantRankLevelSets

universe u𝕜 uE uE' uH uH' uM uN

open Manifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ N]

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the statement
-- shape was matched against the local constant-rank API from `Exercise_4_4`, the embedded
-- submanifold API from `Definition_5_28_extra_1`, and the nearby level-set precedent in
-- `Corollary_5_13`.
-- Proof sketch: apply the constant-rank theorem pointwise on the level set to obtain local slice
-- coordinates of codimension `r`, then package the resulting manifold structure on the fiber.


-- Proof sketch: the level set is the preimage of the closed singleton `{c}` under the continuous
-- map `Φ`, so it is closed in `M`; combine this with the embedded-submanifold structure from (1).
/-- Theorem 5.12 (2) (Constant-Rank Level Set Theorem): each level set of a smooth constant-rank
map is properly embedded in the ambient manifold. -/
theorem constant_rank_level_set_isProperlyEmbedded [T1Space N] {r : ℕ} {Φ : M → N}
    (hΦsmooth : ContMDiff I J ∞ Φ) (hΦrank : HasConstantRank I J Φ r) (c : N) :
    (Φ ⁻¹' {c}).IsProperlyEmbedded := by
  exact (isClosed_singleton.preimage hΦsmooth.continuous).isProperlyEmbedded

end ConstantRankLevelSets

section OrdinaryRealLevelSets

variable {E E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

open Manifold

/-- The constant-rank level-set theorem for ordinary finite-dimensional real manifolds.
The original ambient atlas is retained. The result is C∞, not the legacy analytic
`IsEmbeddedSubmanifold` owner. The source rank bound makes the codimension equality
valid even when the fibre is empty; no nonempty-fibre hypothesis is imposed. -/
theorem constant_rank_level_set_has_embedded_submanifold_structure
    {r : ℕ} {Φ : M → N} (hΦsmooth : ContMDiff I J ∞ Φ)
    (hΦrank : HasConstantRank I J Φ r) (c : N)
    (hrm : r ≤ Module.finrank ℝ E) :
    let k : ℕ := Module.finrank ℝ E - r
    let S : Set M := Φ ⁻¹' {c}
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S,
      ∃ hs : IsManifold (𝓡 k) ∞ S,
        letI := cs
        letI := hs
        IsSmoothEmbedding (𝓡 k) I ∞ (Subtype.val : S → M) ∧
          Module.finrank ℝ E - k = r := by
  obtain ⟨cs, hs, hemb⟩ :=
    LeeVerifiedLevelSets.Generic.constant_rank_level_set_smooth_structure
      hΦsmooth hΦrank c hrm
  exact ⟨cs, hs, hemb, Nat.sub_sub_self hrm⟩

end OrdinaryRealLevelSets
