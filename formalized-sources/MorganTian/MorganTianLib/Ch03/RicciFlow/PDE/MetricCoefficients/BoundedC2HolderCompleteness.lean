import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BoundedC2JetCompleteness
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BoundedHolderGraphNorm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

-- Make the nested operator and bounded-continuous-function metric instances
-- available while Lean elaborates the theorem statement itself.
local instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    NormedAddCommGroup (E3 →L[ℝ] V) := inferInstance
local instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    NormedSpace ℝ (E3 →L[ℝ] V) := inferInstance
local instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    CompleteSpace (E3 →L[ℝ] V) := inferInstance
local instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] V) := inferInstance
local instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] V) := inferInstance
local instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    CompleteSpace (E3 →L[ℝ] E3 →L[ℝ] V) := inferInstance
local instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    MetricSpace (E3 →ᵇ V) := inferInstance
local instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    MetricSpace (E3 →ᵇ (E3 →L[ℝ] V)) := inferInstance
local instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    MetricSpace (E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)) := inferInstance
local instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    MetricSpace (Ω →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)) := inferInstance
local instance (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    MetricSpace ((E3 →ᵇ V) × ((E3 →ᵇ (E3 →L[ℝ] V)) ×
      (E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)))) := inferInstance
def boundedC2HolderJetSet (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (alpha : ℝ) : Set ((E3 →ᵇ V) × ((E3 →ᵇ (E3 →L[ℝ] V)) ×
      ((E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)) × (Ω →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V))))) :=
  {z | (z.1,z.2.1,z.2.2.1) ∈ boundedC2JetSet V ∧
    (z.2.2.1,z.2.2.2) ∈ boundedHolderGraph (E3 →L[ℝ] E3 →L[ℝ] V) alpha}

/-- **Math.** bounded C2 holder completeness. -/
theorem bounded_C2_holder_completeness 
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (alpha : ℝ) :
    IsComplete (boundedC2HolderJetSet V alpha) ∧ ∀ z ∈ boundedC2HolderJetSet V alpha,
      ContDiff ℝ 2 (fun x : E3 => z.1 x) ∧ ∀ x y : E3,
        ‖z.2.2.1 x-z.2.2.1 y‖ ≤ ‖z.2.2.2‖*‖x-y‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  letI : T0Space ((E3 →ᵇ V) × ((E3 →ᵇ (E3 →L[ℝ] V)) ×
      (E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)))) := MetricSpace.instT0Space
  have hjetclosed : IsClosed (boundedC2JetSet V) :=
    (bounded_C2_jet_completeness V).1.isClosed
  have hholderclosed : IsClosed
      (boundedHolderGraph (E3 →L[ℝ] E3 →L[ℝ] V) alpha) :=
    bounded_holder_graph_closed _ alpha
  let jetMap : ((E3 →ᵇ V) × ((E3 →ᵇ (E3 →L[ℝ] V)) ×
      ((E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)) ×
        (Ω →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V))))) →
        ((E3 →ᵇ V) × ((E3 →ᵇ (E3 →L[ℝ] V)) ×
          (E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)))) :=
    fun z => (z.1, (z.2.1, z.2.2.1))
  let holderMap : ((E3 →ᵇ V) × ((E3 →ᵇ (E3 →L[ℝ] V)) ×
      ((E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)) ×
        (Ω →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V))))) →
        ((E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)) ×
          (Ω →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V))) :=
    fun z => (z.2.2.1, z.2.2.2)
  have hjetcont : Continuous jetMap := by
    dsimp [jetMap]
    exact continuous_fst.prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_snd)))
  have hholdercont : Continuous holderMap := by
    dsimp [holderMap]
    exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hclosed : IsClosed (boundedC2HolderJetSet V alpha) := by
    rw [show boundedC2HolderJetSet V alpha =
      jetMap ⁻¹' boundedC2JetSet V ∩
        holderMap ⁻¹' boundedHolderGraph (E3 →L[ℝ] E3 →L[ℝ] V) alpha by
          ext z
          rfl]
    exact (hjetclosed.preimage hjetcont).inter
      (hholderclosed.preimage hholdercont)
  have hambient : CompleteSpace
      ((E3 →ᵇ V) × ((E3 →ᵇ (E3 →L[ℝ] V)) ×
        ((E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V)) ×
          (Ω →ᵇ (E3 →L[ℝ] E3 →L[ℝ] V))))) := inferInstance
  refine ⟨hclosed.isComplete, ?_⟩
  intro z hz
  change (z.1, z.2.1, z.2.2.1) ∈ boundedC2JetSet V ∧
    (z.2.2.1, z.2.2.2) ∈
      boundedHolderGraph (E3 →L[ℝ] E3 →L[ℝ] V) alpha at hz
  rcases hz with ⟨hjet, hholder⟩
  have hregular := (bounded_C2_jet_completeness V).2
    (z.1, (z.2.1, z.2.2.1)) hjet
  refine ⟨hregular, ?_⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    simpa using mul_nonneg (norm_nonneg (z.2.2.2))
      (Real.zero_rpow_nonneg alpha)
  · let p : Ω := ⟨(x, y), hxy⟩
    have hdist : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hpow : 0 < ‖x - y‖ ^ alpha := Real.rpow_pos_of_pos hdist alpha
    have hrel := hholder p
    have hnorm : ‖z.2.2.2 p‖ = (‖x - y‖ ^ alpha)⁻¹ *
        ‖z.2.2.1 x - z.2.2.1 y‖ := by
      rw [hrel, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpow.le)]
    have hpoint : ‖z.2.2.1 x - z.2.2.1 y‖ =
        ‖z.2.2.2 p‖ * ‖x - y‖ ^ alpha := by
      calc
        ‖z.2.2.1 x - z.2.2.1 y‖ =
            ((‖x - y‖ ^ alpha)⁻¹ *
              ‖z.2.2.1 x - z.2.2.1 y‖) * ‖x - y‖ ^ alpha := by
                field_simp
        _ = ‖z.2.2.2 p‖ * ‖x - y‖ ^ alpha := by rw [← hnorm]
    calc
      ‖z.2.2.1 x - z.2.2.1 y‖ =
          ‖z.2.2.2 p‖ * ‖x - y‖ ^ alpha := hpoint
      _ ≤ ‖z.2.2.2‖ * ‖x - y‖ ^ alpha := by
        exact mul_le_mul_of_nonneg_right
          ((z.2.2.2).norm_coe_le_norm p) hpow.le
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
