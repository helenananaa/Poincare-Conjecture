import Mathlib
import LeeSmoothLib.Ch05.Sec05_28.Proposition_5_2
import LeeSmoothLib.Ch08.Sec08_57.Proposition_8_19
import LeeSmoothLib.Ch08.Sec08_63.GraphEmbedding
import LeeSmoothLib.Ch08.Sec08_63.VectorFieldExtensionForward

open Set Function Manifold Topology
open scoped ContDiff Manifold

/-!
# Problem 8.14: extension from the graph

This file formalizes the ordinary finite-dimensional real `C∞` theorem. Both manifolds are
Hausdorff and second countable and both models are boundaryless. This is intentionally not a
complex-analytic statement: global holomorphic extension would already fail for vector fields on
compact curves of genus at least two.

The construction does not identify tangent spaces at different points of `N`. Instead it regards
the graph as a closed embedded submanifold, pushes `X` intrinsically across the diffeomorphism from
`M` to that graph, and applies the forward closed-submanifold extension theorem.
-/

universe uE uE' uH uH' uM uN

noncomputable section

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'}
  [I.Boundaryless] [J.Boundaryless]
  [IsManifold I (∞ : ℕ∞ω) M]
  [IsManifold J (∞ : ℕ∞ω) N]
  [T2Space M] [T2Space N]
  [SecondCountableTopology M] [SecondCountableTopology N]

local notation "SmoothVectorField" => Cₛ^∞⟮I; E, fun x : M ↦ TangentSpace I x⟯
local notation "SmoothProductVectorField" =>
  Cₛ^∞⟮I.prod J; E × E', fun p : M × N ↦ TangentSpace (I.prod J) p⟯
local notation "SmoothMap" => C^∞⟮I, M; J, N⟯

namespace VectorField

/-- Relatedness is transitive under composition of the underlying smooth maps. -/
lemma f_related_comp
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H'']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    {K : ModelWithCorners ℝ E'' H''} [IsManifold K (∞ : ℕ∞ω) P]
    {F : M → N} {G : N → P}
    {X : ∀ x : M, TangentSpace I x}
    {Y : ∀ y : N, TangentSpace J y}
    {Z : ∀ z : P, TangentSpace K z}
    (hFG : f_related G Y Z) (hXY : f_related F X Y) :
    f_related (G ∘ F) X Z := by
  refine ⟨hFG.1.comp hXY.1, ?_⟩
  intro x
  rw [mfderiv_comp_apply x
      (hFG.1.mdifferentiableAt (by simp))
      (hXY.1.mdifferentiableAt (by simp)),
    hXY.2 x, hFG.2 (F x)]
  rfl

end VectorField

/-- The graph of a smooth map is closed in the Hausdorff product. -/
lemma smooth_graph_range_isClosed (f : SmoothMap) :
    IsClosed (Set.range (fun x : M ↦ (x, f x))) := by
  exact Function.LeftInverse.isClosed_range
    (f := (Prod.fst : M × N → M)) (g := fun x : M ↦ (x, f x))
    (fun _ ↦ rfl) continuous_fst (continuous_id.prodMk f.contMDiff.continuous)

/-- Problem 8.14, in the textbook finite-dimensional real smooth setting: every smooth vector
field on `M` has some smooth ambient extension on `M × N` related to it along the graph of `f`.

No global trivialization or pointwise identity transport between distinct tangent fibers is used,
and the resulting ambient field is not asserted to equal the generally nonsmooth naive formula
away from the graph. -/
theorem exists_smooth_graph_related_vector_field
    (f : SmoothMap) (X : SmoothVectorField) :
    ∃ Y : SmoothProductVectorField,
      VectorField.f_related (fun x : M ↦ (x, f x)) X Y := by
  classical
  let graph : M → M × N := fun x ↦ (x, f x)
  have hGraph : Manifold.IsSmoothEmbedding I (I.prod J) (∞ : ℕ∞ω) graph := by
    simpa [graph] using
      graphMap_isSmoothEmbedding_general (I := I) (J := J) (f : M → N) f.contMDiff

  obtain ⟨graphCharted, hInduced⟩ :=
    smooth_embedding_range_has_induced_manifold_structure hGraph
  letI : ChartedSpace H (Set.range graph) := graphCharted
  let graphManifold : IsManifold I (∞ : ℕ∞ω) (Set.range graph) :=
    Classical.choose hInduced
  letI : IsManifold I (∞ : ℕ∞ω) (Set.range graph) := graphManifold
  have hInducedSpec := Classical.choose_spec hInduced
  obtain ⟨hSubtype, graphDiffeomorph, hGraphDiffeomorph⟩ := hInducedSpec

  let Xgraph : Cₛ^∞⟮I; E, fun p : Set.range graph ↦ TangentSpace I p⟯ :=
    ⟨(graphDiffeomorph _* X),
      contMDiff_pushforward_of_diffeomorph graphDiffeomorph X.contMDiff⟩
  have hXgraph :
      VectorField.f_related (graphDiffeomorph : M → Set.range graph) X Xgraph := by
    exact f_related_pushforward_of_diffeomorph graphDiffeomorph X

  have hGraphClosed : IsClosed (Set.range graph) := by
    simpa [graph] using smooth_graph_range_isClosed f
  have hGraphProper : (Set.range graph).IsProperlyEmbedded :=
    hGraphClosed.isProperlyEmbedded

  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace H' := J.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  letI : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  letI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  letI : SigmaCompactSpace N := sigmaCompactSpace_of_locallyCompact_secondCountable

  obtain ⟨Y, hY⟩ :=
    VectorFieldExtensionForward.exists_global_vectorField_extension_of_isProperlyEmbedded
      (I := I.prod J) (J := I) hSubtype hGraphProper Xgraph
  refine ⟨Y, ?_⟩

  have hComposed :
      VectorField.f_related
        ((Subtype.val : Set.range graph → M × N) ∘ graphDiffeomorph) X Y :=
    VectorField.f_related_comp hY hXgraph
  have hMap :
      ((Subtype.val : Set.range graph → M × N) ∘ graphDiffeomorph) = graph := by
    funext x
    exact hGraphDiffeomorph x
  simpa [hMap, graph] using hComposed

end
