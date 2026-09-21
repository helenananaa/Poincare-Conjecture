import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

open Set Function Riemannian Bundle
open scoped ContDiff Manifold Topology Bundle
noncomputable section
namespace MorganTianLib.SurgeryInterpolation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Actual smooth positive metric from smooth nonnegative weights. -/
theorem exists_weighted_riemannianMetric (g0 g1 : RiemannianMetric I M)
    (a b : M → ℝ) (ha : ContMDiff I 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x)
    (hpos : ∀ x, 0 < a x + b x) :
    ∃ g : RiemannianMetric I M, ∀ x v w,
      g.metricInner x v w = a x * g0.metricInner x v w + b x * g1.metricInner x v w := by
/- SWARM_PROOF_BEGIN -/
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g0.toRiemannianMetric⟩
  have hweighted_pos : ∀ x (v : TangentSpace I x), v ≠ 0 →
      0 < a x * g0.inner x v v + b x * g1.inner x v v := by
    intro x v hv
    have h0 : 0 < g0.inner x v v := g0.pos x v hv
    have h1 : 0 < g1.inner x v v := g1.pos x v hv
    have hcases : 0 < a x ∨ 0 < b x := by
      by_cases ha' : 0 < a x
      · exact Or.inl ha'
      · right
        nlinarith [hpos x, ha0 x]
    rcases hcases with ha' | hb'
    · have hleft : 0 < a x * g0.inner x v v := mul_pos ha' h0
      have hright : 0 ≤ b x * g1.inner x v v :=
        mul_nonneg (hb0 x) (le_of_lt h1)
      linarith
    · have hleft : 0 ≤ a x * g0.inner x v v :=
        mul_nonneg (ha0 x) (le_of_lt h0)
      have hright : 0 < b x * g1.inner x v v := mul_pos hb' h1
      linarith
  refine ⟨{
    inner := fun x => a x • g0.inner x + b x • g1.inner x
    symm := ?_
    pos := ?_
    isVonNBounded := ?_
    contMDiff := ?_ }, ?_⟩
  · intro x v w
    change a x * g0.inner x v w + b x * g1.inner x v w =
      a x * g0.inner x w v + b x * g1.inner x w v
    rw [g0.symm, g1.symm]
  · intro x v hv
    change 0 < a x * g0.inner x v v + b x * g1.inner x v v
    exact hweighted_pos x v hv
  · intro x
    apply isVonNBounded_of_posDef
    intro v hv
    exact hweighted_pos x v hv
  · exact (ContMDiff.smul_section ha g0.contMDiff).add_section
      (ContMDiff.smul_section hb g1.contMDiff)
  · intro x v w
    rfl
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryInterpolation
