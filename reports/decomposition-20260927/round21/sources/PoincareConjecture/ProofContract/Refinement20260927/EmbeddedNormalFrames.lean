import PoincareConjecture.ProofContract.Refinement20260927.AcceptedTwentyNine
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
open scoped Topology Manifold ContDiff BigOperators
/-- **Math.** The normal fiber is defined by the actual derivative of the supplied embedding. -/
def embeddedNormalSpace {N : CompactSmoothThree.{u}} {n : ℕ}
    (e : CompactEuclideanEmbedding N n) (p : N) : Submodule ℝ (ApproxAmbient n) :=
  (LinearMap.range (mfderiv (𝓡 3) 𝓘(ℝ,ApproxAmbient n) e.map p).toLinearMap)ᗮ
/-- **Math.** The actual normal total space, with the induced product topology. -/
abbrev EmbeddedNormalTotal {N : CompactSmoothThree.{u}} {n : ℕ}
    (e : CompactEuclideanEmbedding N n) :=
  {z : N × ApproxAmbient n // z.2 ∈ embeddedNormalSpace e z.1}
def embeddedNormalZero {N : CompactSmoothThree.{u}} {n : ℕ}
    (e : CompactEuclideanEmbedding N n) (p : N) : EmbeddedNormalTotal e :=
  ⟨(p,0), (embeddedNormalSpace e p).zero_mem⟩
/-- **Math.** An ordinary smooth base chart and local orthonormal normal frame.
Neither a normal-bundle parameter chart nor an endpoint inverse is a field. -/
structure EmbeddedNormalFrameAt {N : CompactSmoothThree.{u}} {n : ℕ}
    (e : CompactEuclideanEmbedding N n) (p : N) where
  baseChart : OpenPartialHomeomorph N NormalTangent
  point_source : p ∈ baseChart.source
  smooth_base_inverse : ContMDiffOn 𝓘(ℝ,NormalTangent) (𝓡 3) ∞ baseChart.symm baseChart.target
  smooth_embedding : ContDiffOn ℝ ∞ (e.map ∘ baseChart.symm) baseChart.target
  linear : NormalTangent →L[ℝ] ApproxAmbient n
  linear_injective : Function.Injective linear
  embedding_deriv : HasFDerivAt (e.map ∘ baseChart.symm) linear (baseChart p)
  center_normal : embeddedNormalSpace e p = NormalFiber linear
  count : ℕ
  frame : Fin count → N → ApproxAmbient n
  continuous_frame : ∀ i, ContinuousOn (frame i) baseChart.source
  smooth_frame : ∀ i, ContDiffOn ℝ ∞ (frame i ∘ baseChart.symm) baseChart.target
  orthonormal : ∀ q ∈ baseChart.source, Orthonormal ℝ (fun i => frame i q)
  spans : ∀ q ∈ baseChart.source,
    Submodule.span ℝ (range (fun i => frame i q)) = embeddedNormalSpace e q
/-- **Math.** Independent existence leaf, to reuse the already audited Lee normal frames. -/
def EmbeddedNormalFrameStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (n : ℕ) (e : CompactEuclideanEmbedding N n) (p : N),
    Nonempty (EmbeddedNormalFrameAt e p)
/-- **Math.** Literal finite-sum transport; no arbitrary unrelated isomorphism is chosen. -/
def normalFrameForward {N : CompactSmoothThree.{u}} {n : ℕ}
    {e : CompactEuclideanEmbedding N n} {p : N} (F : EmbeddedNormalFrameAt e p)
    (q : N) : ApproxAmbient n →L[ℝ] ApproxAmbient n :=
  ∑ i : Fin F.count, (innerSL ℝ (F.frame i p)).smulRight (F.frame i q)
def normalFrameBackward {N : CompactSmoothThree.{u}} {n : ℕ}
    {e : CompactEuclideanEmbedding N n} {p : N} (F : EmbeddedNormalFrameAt e p)
    (q : N) : ApproxAmbient n →L[ℝ] ApproxAmbient n :=
  ∑ i : Fin F.count, (innerSL ℝ (F.frame i q)).smulRight (F.frame i p)
/-- **Math.** Local properties of these same two finite sums. -/
structure NormalFrameTransportLaws {N : CompactSmoothThree.{u}} {n : ℕ}
    {e : CompactEuclideanEmbedding N n} {p : N} (F : EmbeddedNormalFrameAt e p) : Prop where
  continuous_forward : ContinuousOn (normalFrameForward F) F.baseChart.source
  continuous_backward : ContinuousOn (normalFrameBackward F) F.baseChart.source
  smooth_forward : ContDiffOn ℝ ∞ (normalFrameForward F ∘ F.baseChart.symm) F.baseChart.target
  forward_mem : ∀ q ∈ F.baseChart.source, ∀ v ∈ NormalFiber F.linear,
    normalFrameForward F q v ∈ embeddedNormalSpace e q
  backward_mem : ∀ q ∈ F.baseChart.source, ∀ v ∈ embeddedNormalSpace e q,
    normalFrameBackward F q v ∈ NormalFiber F.linear
  backward_forward : ∀ q ∈ F.baseChart.source, ∀ v ∈ NormalFiber F.linear,
    normalFrameBackward F q (normalFrameForward F q v) = v
  forward_backward : ∀ q ∈ F.baseChart.source, ∀ v ∈ embeddedNormalSpace e q,
    normalFrameForward F q (normalFrameBackward F q v) = v
  center_identity : ∀ v : NormalFiber F.linear, normalFrameForward F p v = v
/-- **Math.** Independent finite-dimensional algebra and finite-sum regularity leaf. -/
def NormalFrameTransportStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (n : ℕ) (e : CompactEuclideanEmbedding N n)
    (p : N) (F : EmbeddedNormalFrameAt e p), NormalFrameTransportLaws F
/-- **Math.** A parameter chart, with its exact source, target and inverse formula.
It is not a local inverse of the endpoint map. -/
structure NormalBundleParametrization {N : CompactSmoothThree.{u}} {n : ℕ}
    {e : CompactEuclideanEmbedding N n} {p : N} (F : EmbeddedNormalFrameAt e p) where
  chart : OpenPartialHomeomorph (EmbeddedNormalTotal e) (NormalSplit F.linear)
  source_eq : chart.source = {z | z.val.1 ∈ F.baseChart.source}
  target_eq : chart.target = F.baseChart.target ×ˢ univ
  zero_chart : chart (embeddedNormalZero e p) = (F.baseChart p,0)
  inverse_base : ∀ z ∈ chart.target, (chart.symm z).val.1 = F.baseChart.symm z.1
  inverse_vector : ∀ z ∈ chart.target,
    (chart.symm z).val.2 = normalFrameForward F (F.baseChart.symm z.1) z.2
/-- **Math.** Independent topological construction on the actual induced normal total space. -/
def NormalBundleParametrizationStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (n : ℕ) (e : CompactEuclideanEmbedding N n)
    (p : N) (F : EmbeddedNormalFrameAt e p), NormalFrameTransportLaws F →
      Nonempty (NormalBundleParametrization F)
/-- **Math.** Independent calculus leaf, valid for any chart with those exact formulas. -/
def NormalParametrizationRegularityStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (n : ℕ) (e : CompactEuclideanEmbedding N n)
    (p : N) (F : EmbeddedNormalFrameAt e p) (h : NormalFrameTransportLaws F)
    (r : NormalBundleParametrization F),
      ContDiffOn ℝ ∞ (fun z : NormalSplit F.linear => e.map (F.baseChart.symm z.1) +
        normalFrameForward F (F.baseChart.symm z.1) z.2) r.chart.target ∧
      ContMDiffOn 𝓘(ℝ,NormalSplit F.linear) (𝓡 3) ∞
        (fun z => (r.chart.symm z).val.1) r.chart.target
/-- **Math.** No normal coordinate or frame witness is assumed by this existence target. -/
def EmbeddedNormalCoordinatesStatement : Prop :=
  ∀ (N : CompactSmoothThree.{u}) (n : ℕ) (e : CompactEuclideanEmbedding N n),
    Nonempty (NormalCoordinateTube e)
theorem embeddedNormalZero_base {N : CompactSmoothThree.{u}} {n : ℕ}
    (e : CompactEuclideanEmbedding N n) (p : N) : (embeddedNormalZero e p).val.1 = p := rfl
#print axioms embeddedNormalZero_base
end PoincareConjecture.ProofContract.Refinement20260927
