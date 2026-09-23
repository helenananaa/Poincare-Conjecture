import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BoundedDerivativeGraph
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)
def boundedC2JetSet (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Set ((E3 →ᵇ V) × ((E3 →ᵇ (E3 →L[ℝ] V)) × (E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)))) :=
  {z | (∀ x : E3, HasFDerivAt (fun y : E3 => z.1 y) (z.2.1 x) x) ∧
       (∀ x : E3, HasFDerivAt (fun y : E3 => z.2.1 y) (z.2.2 x) x)}

/-- **Math.** bounded C2 jet completeness. -/
theorem bounded_C2_jet_completeness 
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    IsComplete (boundedC2JetSet V) ∧ ∀ z ∈ boundedC2JetSet V,
      ContDiff ℝ 2 (fun x : E3 => z.1 x) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : NormedAddCommGroup (E3 →L[ℝ] V) := inferInstance
  letI : NormedSpace ℝ (E3 →L[ℝ] V) := inferInstance
  letI : CompleteSpace (E3 →L[ℝ] V) := inferInstance
  letI : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] V) := inferInstance
  letI : CompleteSpace (E3 →L[ℝ] E3 →L[ℝ] V) := inferInstance
  letI : MetricSpace (E3 →ᵇ V) := inferInstance
  letI : MetricSpace (E3 →ᵇ (E3 →L[ℝ] V)) := inferInstance
  letI : MetricSpace (E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)) := inferInstance
  letI : FirstCountableTopology ((E3 →ᵇ V) × (E3 →ᵇ (E3 →L[ℝ] V)) × (E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V))) := inferInstance
  have hclosed : IsClosed (boundedC2JetSet V) := by
    apply IsSeqClosed.isClosed
    intro seq q hz hlim
    have hfirstlim :
        Tendsto (fun n => ((seq n).1, (seq n).2.1)) atTop (𝓝 (q.1, q.2.1)) := by
      simpa only [Function.comp_def] using
        ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).tendsto q).comp hlim
    have hsecondlim :
        Tendsto (fun n => ((seq n).2.1, (seq n).2.2)) atTop (𝓝 (q.2.1, q.2.2)) := by
      simpa only [Function.comp_def] using
        (((continuous_fst.comp continuous_snd).prodMk
          (continuous_snd.comp continuous_snd)).tendsto q).comp hlim
    have hfirstmem :
        (q.1, q.2.1) ∈ boundedDerivativeGraph V := by
      apply (bounded_derivative_graph_closed V).mem_of_tendsto hfirstlim
      exact Filter.Eventually.of_forall fun n => (hz n).1
    have hsecondmem :
        (q.2.1, q.2.2) ∈ boundedDerivativeGraph (E3 →L[ℝ] V) := by
      apply (bounded_derivative_graph_closed (E3 →L[ℝ] V)).mem_of_tendsto hsecondlim
      exact Filter.Eventually.of_forall fun n => (hz n).2
    change (∀ x : E3, HasFDerivAt (fun y : E3 => q.1 y) (q.2.1 x) x) ∧
      (∀ x : E3, HasFDerivAt (fun y : E3 => q.2.1 y) (q.2.2 x) x)
    exact ⟨hfirstmem, hsecondmem⟩
  have hambient : CompleteSpace
      ((E3 →ᵇ V) × ((E3 →ᵇ (E3 →L[ℝ] V)) ×
        (E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)))) := inferInstance
  refine ⟨hclosed.isComplete, ?_⟩
  intro z hz
  change (∀ x : E3, HasFDerivAt (fun y : E3 => z.1 y) (z.2.1 x) x) ∧
    (∀ x : E3, HasFDerivAt (fun y : E3 => z.2.1 y) (z.2.2 x) x) at hz
  rcases hz with ⟨hderiv, hsecond⟩
  have hgradient : ContDiff ℝ 1 (fun x : E3 => z.2.1 x) := by
    apply contDiff_one_iff_hasFDerivAt.mpr
    exact ⟨fun x => z.2.2 x, z.2.2.continuous, hsecond⟩
  have hdiff : Differentiable ℝ (fun x : E3 => z.1 x) := by
    intro x
    exact (hderiv x).differentiableAt
  have hderivative :
      fderiv ℝ (fun x : E3 => z.1 x) = fun x => z.2.1 x := by
    funext x
    exact (hderiv x).fderiv
  have hfunction : ContDiff ℝ 2 (fun x : E3 => z.1 x) := by
    rw [show (2 : ℕ∞ω) = (1 : ℕ∞ω) + 1 by norm_num,
      contDiff_succ_iff_fderiv]
    refine ⟨hdiff, ?_, ?_⟩
    · intro htop
      simp at htop
    · simpa only [hderivative] using hgradient
  exact hfunction
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
