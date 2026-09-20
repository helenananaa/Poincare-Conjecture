import LeeSmoothLib.Verified.LevelSets.Generic
import Mathlib
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_2
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section RegularLevelSets

universe uE uE' uH uH' uM uN

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the statement
-- shape was matched against the local regular-value owner in `Definition_5_36_extra_3` and the
-- preceding submersion-level-set corollary in `Corollary_5_13`.



/-- Corollary 5.14 (2) (Regular Level Set Theorem): if `Φ : M → N` is smooth and `c` is a regular
value of `Φ`, then the level set `Φ ⁻¹' {c}` is properly embedded in `M`. -/
theorem regular_level_set_isProperlyEmbedded [T1Space N] {Φ : M → N} {c : N}
    (hΦ : ContMDiff I J ∞ Φ) (hc : IsRegularValue I J Φ c) :
    (Φ ⁻¹' {c}).IsProperlyEmbedded := by
  exact (isClosed_singleton.preimage hΦ.continuous).isProperlyEmbedded

end RegularLevelSets

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

/-- The regular-level theorem in ordinary finite-dimensional real boundaryless models.
The conclusion carries a C∞ embedding, not an unjustified analytic inclusion. The explicit
dimension bound is needed for the codimension equality when the fibre is empty. -/
theorem regular_level_set_has_embedded_submanifold_structure {Φ : M → N} {c : N}
    (hΦ : ContMDiff I J ∞ Φ) (hc : IsRegularValue I J Φ c)
    (hnm : Module.finrank ℝ E' ≤ Module.finrank ℝ E) :
    let k : ℕ := Module.finrank ℝ E - Module.finrank ℝ E'
    let S : Set M := Φ ⁻¹' {c}
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S,
      ∃ hs : IsManifold (𝓡 k) ∞ S,
        letI := cs
        letI := hs
        IsSmoothEmbedding (𝓡 k) I ∞ (Subtype.val : S → M) ∧
          Module.finrank ℝ E - k = Module.finrank ℝ E' := by
  obtain ⟨cs, hs, hemb⟩ :=
    LeeVerifiedLevelSets.Generic.regular_level_set_smooth_structure hΦ hc hnm
  exact ⟨cs, hs, hemb, Nat.sub_sub_self hnm⟩

end OrdinaryRealLevelSets
