import PoincareConjecture.ParallelImplementation.UniformStationaryBackgroundDifference
import PoincareConjecture.ParallelImplementation.ForcingGraphLinearLift
import PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.EncodedStationaryDifference
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "A" => E3 →L[ℝ] E3
local notation "V" => E3 →L[ℝ] E6
local notation "H" => E3 →L[ℝ] E3 →L[ℝ] E6
local instance : NormedAddCommGroup A := inferInstance
local instance : NormedSpace ℝ A := inferInstance
local instance : NormedAddCommGroup V := inferInstance
local instance : NormedSpace ℝ V := inferInstance
local instance : NormedAddCommGroup H := inferInstance
local instance : NormedSpace ℝ H := inferInstance
/-- Bound the actual metric background and stationary Hessian-trace forcing
used in the unforced affine PDE; these terms are not set to zero. -/
theorem uniform_encoded_stationary_differences
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (E : E6 →L[ℝ] A) (hE : ‖E‖ ≤ 3)
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 ≤ T →
      ∀ (Fu : ForcingJet E6 T) (FA : ForcingJet V T) (FH : ForcingJet H T),
        Fu ∈ forcingGraph E6 T alpha → FA ∈ forcingGraph V T alpha →
        FH ∈ forcingGraph H T alpha →
        (∀ p : Slab T, Fu.1 p = u p.2) →
        (∀ p : Slab T, FA.1 p = fderiv ℝ u p.2) →
        (∀ p : Slab T, FH.1 p = fderiv ℝ (fderiv ℝ u) p.2) →
        ∀ (a : ForcingJet A T) (f : ForcingJet E6 T),
          a ∈ forcingGraph A T alpha → f ∈ forcingGraph E6 T alpha →
          (∀ p : Slab T, a.1 p = -E (Fu.1 p)) →
          (∀ p : Slab T, f.1 p = ∑ j : Fin 3,
            FH.1 p (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) →
          ∀ (i : Fin 3) (h : ℝ), h ≠ 0 →
            ‖h⁻¹ • (translateForcingJet i h a - a)‖ ≤ C ∧
            ‖h⁻¹ • (translateForcingJet i h FA - FA)‖ ≤ C ∧
            ‖h⁻¹ • (translateForcingJet i h FH - FH)‖ ≤ C ∧
            ‖h⁻¹ • (translateForcingJet i h f - f)‖ ≤ C :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨K, hKpos, hstationary⟩ :=
    PoincareConjecture.ParallelImplementation.UniformStationaryBackgroundDifference.uniform_stationary_background_differences
      u hu hc alpha ha ha1
  have hKnonneg : 0 ≤ K := le_of_lt hKpos
  let graphSubmodule {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      (T alpha : ℝ) : Submodule ℝ (ForcingJet W T) := {
    carrier := forcingGraph W T alpha
    zero_mem' := by intro p; simp
    add_mem' := by
      intro z w hz hw p
      change z.2 p+w.2 p =
        (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((z.1+w.1) p.1.1-(z.1+w.1) p.1.2)
      rw [hz p, hw p]
      simp [sub_eq_add_neg, smul_add]
      abel
    smul_mem' := by
      intro c z hz p
      change c • z.2 p =
        (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((c • z.1) p.1.1-(c • z.1) p.1.2)
      rw [hz p]
      simp [smul_sub, smul_smul, mul_comm]
  }
  let negE : E6 →L[ℝ] A := -E
  have hnegE : ‖negE‖ ≤ 3 := by simpa [negE] using hE
  let e (j : Fin 3) : E3 := EuclideanSpace.single j 1
  let tr : H →L[ℝ] E6 :=
    ∑ j : Fin 3, (ContinuousLinearMap.apply ℝ E6 (e j)).comp
      (ContinuousLinearMap.apply ℝ (E3 →L[ℝ] E6) (e j))
  have htr (G : H) : ‖tr G‖ ≤ 3 * ‖G‖ := by
    change ‖∑ j : Fin 3, G (e j) (e j)‖ ≤ 3 * ‖G‖
    calc
      ‖∑ j : Fin 3, G (e j) (e j)‖ ≤ ∑ j : Fin 3, ‖G (e j) (e j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, ‖G‖ := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ‖G (e j) (e j)‖ ≤ ‖G (e j)‖ * ‖e j‖ := (G (e j)).le_opNorm _
          _ ≤ (‖G‖ * ‖e j‖) * ‖e j‖ :=
            mul_le_mul_of_nonneg_right (G.le_opNorm _) (norm_nonneg _)
          _ = ‖G‖ := by simp [e]
      _ = 3 * ‖G‖ := by simp
  have htrnorm : ‖tr‖ ≤ 3 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro G
    exact htr G
  refine ⟨3*K, by positivity, ?_⟩
  intro T' hT Fu FA FH hFuGraph hFAGraph hFHGraph hFuval hFAval hFHval
    a f haGraph hfGraph haval hfval i h hne
  obtain ⟨LiftE, hLiftEnorm, hLiftEval, hLiftEinc, hLiftEgraph⟩ :=
    PoincareConjecture.ParallelImplementation.ForcingGraphLinearLift.exists_forcing_graph_linear_lift
      negE T' alpha
  have hLiftEnorm3 : ‖LiftE‖ ≤ 3 := hLiftEnorm.trans hnegE
  obtain ⟨LiftTr, hLiftTrnorm, hLiftTrval, hLiftTrinc, hLiftTrgraph⟩ :=
    PoincareConjecture.ParallelImplementation.ForcingGraphLinearLift.exists_forcing_graph_linear_lift
      tr T' alpha
  have hLiftTrnorm3 : ‖LiftTr‖ ≤ 3 := hLiftTrnorm.trans htrnorm
  have hsource := hstationary T' hT Fu FA FH hFuGraph hFAGraph hFHGraph
    hFuval hFAval hFHval i h hne
  have hFuquot : ‖h⁻¹ • (translateForcingJet i h Fu-Fu)‖ ≤ K := hsource.1
  have hFAquot : ‖h⁻¹ • (translateForcingJet i h FA-FA)‖ ≤ K := hsource.2.1
  have hFHquot : ‖h⁻¹ • (translateForcingJet i h FH-FH)‖ ≤ K := hsource.2.2

  have hLiftFuGraph : LiftE Fu ∈ forcingGraph A T' alpha := hLiftEgraph Fu hFuGraph
  have haValue (p : Slab T') : a.1 p = (LiftE Fu).1 p := by
    calc
      a.1 p = -E (Fu.1 p) := haval p
      _ = negE (Fu.1 p) := rfl
      _ = (LiftE Fu).1 p := (hLiftEval Fu p).symm
  have haEq : a = LiftE Fu :=
    PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T' alpha a (LiftE Fu) haGraph hLiftFuGraph haValue

  have hLiftFHGraph : LiftTr FH ∈ forcingGraph E6 T' alpha := hLiftTrgraph FH hFHGraph
  have hfValue (p : Slab T') : f.1 p = (LiftTr FH).1 p := by
    rw [hfval p, hLiftTrval FH p]
    simp [tr, e]
  have hfEq : f = LiftTr FH :=
    PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T' alpha f (LiftTr FH) hfGraph hLiftFHGraph hfValue

  let aq : ForcingJet A T' := h⁻¹ • (translateForcingJet i h a-a)
  let fq : ForcingJet E6 T' := h⁻¹ • (translateForcingJet i h f-f)
  let uq : ForcingJet E6 T' := h⁻¹ • (translateForcingJet i h Fu-Fu)
  let hq : ForcingJet H T' := h⁻¹ • (translateForcingJet i h FH-FH)
  have haqGraph : aq ∈ forcingGraph A T' alpha := by
    change aq ∈ graphSubmodule (W := A) T' alpha
    exact (graphSubmodule (W := A) T' alpha).smul_mem _
      ((graphSubmodule (W := A) T' alpha).sub_mem
        ((PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation.forcing_translation_properties
          T' alpha i h).1 a |>.2 haGraph) haGraph)
  have hfqGraph : fq ∈ forcingGraph E6 T' alpha := by
    change fq ∈ graphSubmodule (W := E6) T' alpha
    exact (graphSubmodule (W := E6) T' alpha).smul_mem _
      ((graphSubmodule (W := E6) T' alpha).sub_mem
        ((PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation.forcing_translation_properties
          T' alpha i h).1 f |>.2 hfGraph) hfGraph)
  have huqGraph : uq ∈ forcingGraph E6 T' alpha := by
    change uq ∈ graphSubmodule (W := E6) T' alpha
    exact (graphSubmodule (W := E6) T' alpha).smul_mem _
      ((graphSubmodule (W := E6) T' alpha).sub_mem
        ((PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation.forcing_translation_properties
          T' alpha i h).1 Fu |>.2 hFuGraph) hFuGraph)
  have hhqGraph : hq ∈ forcingGraph H T' alpha := by
    change hq ∈ graphSubmodule (W := H) T' alpha
    exact (graphSubmodule (W := H) T' alpha).smul_mem _
      ((graphSubmodule (W := H) T' alpha).sub_mem
        ((PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation.forcing_translation_properties
          T' alpha i h).1 FH |>.2 hFHGraph) hFHGraph)
  have hLiftUqGraph : LiftE uq ∈ forcingGraph A T' alpha := hLiftEgraph uq huqGraph
  have hLiftHqGraph : LiftTr hq ∈ forcingGraph E6 T' alpha := hLiftTrgraph hq hhqGraph
  have haqValue (p : Slab T') : aq.1 p = (LiftE uq).1 p := by
    simp [aq, uq, translateForcingJet, PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
      PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialShiftSlabMap,
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint,
      hLiftEval, haval, negE]
  have hfqValue (p : Slab T') : fq.1 p = (LiftTr hq).1 p := by
    simp [fq, hq, translateForcingJet, PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
      PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialShiftSlabMap,
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint,
      hLiftTrval, hfval, tr, e]
  have haqEq : aq = LiftE uq :=
    PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T' alpha aq (LiftE uq) haqGraph hLiftUqGraph haqValue
  have hfqEq : fq = LiftTr hq :=
    PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T' alpha fq (LiftTr hq) hfqGraph hLiftHqGraph hfqValue
  have haqBound : ‖aq‖ ≤ 3*K := by
    rw [haqEq]
    calc
      ‖LiftE uq‖ ≤ ‖LiftE‖ * ‖uq‖ := LiftE.le_opNorm uq
      _ ≤ 3 * ‖uq‖ := mul_le_mul_of_nonneg_right hLiftEnorm3 (norm_nonneg _)
      _ ≤ 3 * K := mul_le_mul_of_nonneg_left hFuquot (by norm_num)
  have hfqBound : ‖fq‖ ≤ 3*K := by
    rw [hfqEq]
    calc
      ‖LiftTr hq‖ ≤ ‖LiftTr‖ * ‖hq‖ := LiftTr.le_opNorm hq
      _ ≤ 3 * ‖hq‖ := mul_le_mul_of_nonneg_right hLiftTrnorm3 (norm_nonneg _)
      _ ≤ 3 * K := mul_le_mul_of_nonneg_left hFHquot (by norm_num)
  have hFAactual : ‖h⁻¹ • (translateForcingJet i h FA-FA)‖ ≤ 3*K := by
    exact hFAquot.trans (by nlinarith [hKnonneg])
  have hFHactual : ‖h⁻¹ • (translateForcingJet i h FH-FH)‖ ≤ 3*K := by
    exact hFHquot.trans (by nlinarith [hKnonneg])
  exact ⟨by simpa [aq] using haqBound, hFAactual, hFHactual,
    by simpa [fq] using hfqBound⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.EncodedStationaryDifference
