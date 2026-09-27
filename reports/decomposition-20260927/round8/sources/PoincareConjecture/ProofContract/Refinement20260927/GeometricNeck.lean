import PoincareConjecture.ProofContract.Refinement20260927.AcceptedTwelve
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MorganTianLib
open scoped Topology Manifold ContDiff
/-- **Math.** One actual metric epsilon-neck inside the input component.
The region is not required to be the whole closed manifold. -/
structure AmbientMetricNeck (M : ClosedThreeManifold.{u}) where
  region : SmoothVolumeRegion.{u}
  metric : Riemannian.RiemannianMetric (𝓡 3) region
  center : region
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  neck : EpsilonNeckStructure epsilon metric center
  inclusion : region → M
  inclusion_open : Topology.IsOpenEmbedding inclusion
/-- **Math.** The fixed closed subcylinder uses half the available axial length. -/
def AmbientMetricNeck.closedParameter {M : ClosedThreeManifold.{u}} (n : AmbientMetricNeck M)
    (q : Sphere2 × Icc (-1 : ℝ) 1) : epsilonNeckDomain n.epsilon :=
  ⟨(q.1, EuclideanSpace.single 0 ((q.2 : ℝ) / (2*n.epsilon))), by
    have he : 0 < 2*n.epsilon := mul_pos (by norm_num) n.epsilon_pos
    change -n.epsilon⁻¹ < (q.2 : ℝ)/(2*n.epsilon) ∧
      (q.2 : ℝ)/(2*n.epsilon) < n.epsilon⁻¹
    constructor
    · apply (lt_div_iff₀ he).mpr
      have hi : n.epsilon⁻¹*n.epsilon = 1 := inv_mul_cancel₀ n.epsilon_pos.ne'
      nlinarith [q.2.2.1]
    · apply (div_lt_iff₀ he).mpr
      have hi : n.epsilon⁻¹*n.epsilon = 1 := inv_mul_cancel₀ n.epsilon_pos.ne'
      nlinarith [q.2.2.2]⟩
def AmbientMetricNeck.closedCollar {M : ClosedThreeManifold.{u}} (n : AmbientMetricNeck M) :
    Sphere2 × Icc (-1 : ℝ) 1 → M := fun q => n.inclusion (n.neck.phi (n.closedParameter q))
/-- **Math.** New independent leaf: prove embedding for this explicit map,
not for an unspecified replacement collar. -/
def EpsilonNeckEmbeddingStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) (n : AmbientMetricNeck M), Topology.IsEmbedding n.closedCollar
/-- **Math.** On the central slice the SAME metric neck parametrization is used. -/
theorem AmbientMetricNeck.central_formula {M : ClosedThreeManifold.{u}}
    (n : AmbientMetricNeck M) (s : Sphere2) :
    n.closedCollar (s, ⟨0, by norm_num⟩) =
      n.inclusion (n.neck.phi ⟨(s,0), by
        constructor <;> simpa using inv_pos.mpr n.epsilon_pos⟩) := by
  unfold AmbientMetricNeck.closedCollar
  congr 2
  apply Subtype.ext
  simp [AmbientMetricNeck.closedParameter]
def metricNeckCut (embed : EpsilonNeckEmbeddingStatement.{u})
    {M : ClosedThreeManifold.{u}} (hsc : SimplyConnectedSpace M)
    (n : AmbientMetricNeck M) (p : Sphere2) : RegularClosedCut M :=
  checked_neck_cut hsc n.closedCollar (embed M n) p
theorem metricNeck_connectedSum (embed : EpsilonNeckEmbeddingStatement.{u})
    {M : ClosedThreeManifold.{u}} (hsc : SimplyConnectedSpace M)
    (n : AmbientMetricNeck M) (p : Sphere2) :
    Nonempty (ConnectedSumPresentation
      (cappedManifold checked_cap_chart checked_interior_open (metricNeckCut embed hsc n p).left.regularPiece)
      (cappedManifold checked_cap_chart checked_interior_open (metricNeckCut embed hsc n p).right.regularPiece) M) :=
  checked_neck_connectedSum hsc n.closedCollar (embed M n) p
#print axioms AmbientMetricNeck.central_formula
#print axioms metricNeckCut
#print axioms metricNeck_connectedSum
end PoincareConjecture.ProofContract.Refinement20260927
