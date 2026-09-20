import MorganTianLib.Ch01.CurvatureNormManifold
import MorganTianLib.Ch03.RicciFlow.MetricDistortion
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4RicciSectional

open scoped ContDiff Manifold Topology Bundle
open Riemannian

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [NeZero (Module.finrank ℝ E)]

/-- **Math.** Sharp Ricci lower bound from a curvature-operator bound: `|Rm| ≤ K` implies

  `Ric(v,v) ≥ -(n-1) K g(v,v)`.

The existing `abs_ricciTensorAt_le_finrank_mul_of_hasCurvatureOperatorNormLeAt`
is the coarser `|Ric| ≤ n K g` estimate. This lemma uses the trace of `n-1`
sectional planes. No Ricci flow, no injectivity radius, no volume comparison. -/
theorem ricciTensorAt_ge_neg_finrank_sub_one_mul
    (g : RiemannianMetric I M) {K : ℝ} (hK : 0 ≤ K) (p : M)
    (hRm : HasCurvatureOperatorNormLeAt g g.leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita g) p K)
    (v : TangentSpace I p) :
    -((Module.finrank ℝ E : ℝ) - 1) * K * g.metricInner p v v ≤
      ricciTensorAt g p v v :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let hLC := canonicalLeviCivita_isLeviCivita g
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hB : IsAlgCurvatureForm
      (curvatureFormAt g g.leviCivitaConnection p) :=
    isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC p
  have hform_eq (w : TangentSpace I p) :
      ricciForm hB w w = ricciTensorAt g p w w := by
    let b := stdOrthonormalBasis ℝ (TangentSpace I p)
    simp only [ricciTensorAt, ricciBilin_apply]
    rw [ricciForm_eq_sum hB w w b, ricciForm_eq_sum _ w w b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [curvatureFormAt_def]
    exact (g.leviCivitaConnection.curvatureFormAt_eq g p
      (extendVector_apply p w) (extendVector_apply p (b i))
      (extendVector_apply p w) (extendVector_apply p (b i))).symm
  by_cases hv : v = 0
  · subst hv
    simp
  · set nv : ℝ := ‖v‖
    set u : TangentSpace I p := nv⁻¹ • v
    have hvn : nv ≠ 0 := norm_ne_zero_iff.mpr hv
    have hu : ‖u‖ = 1 := by
      dsimp [u, nv]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
      exact inv_mul_cancel₀ hvn
    have hv_eq : v = nv • u := by
      simp [u, smul_smul, mul_inv_cancel₀ hvn]
    have hcard : Module.finrank ℝ (TangentSpace I p) =
        Fintype.card (Fin (Module.finrank ℝ E)) :=
      (Fintype.card_fin _).symm
    have hsingle : Orthonormal ℝ
        (Set.restrict ({0} : Set (Fin (Module.finrank ℝ E))) (fun _ => u)) := by
      constructor
      · intro i
        simpa using hu
      · intro i j hij
        exact absurd (Subtype.ext ((Set.mem_singleton_iff.mp i.2).trans
          (Set.mem_singleton_iff.mp j.2).symm)) hij
    obtain ⟨e, he⟩ := hsingle.exists_orthonormalBasis_extension_of_card_eq hcard
    have he0 : e 0 = u := he 0 rfl
    have hKsec : ∀ i ∈ Finset.univ.erase (0 : Fin (Module.finrank ℝ E)),
        -K ≤ sectionalCurvature (curvatureFormAt g g.leviCivitaConnection p)
          (e 0) (e i) := by
      intro i _hi
      simpa [sectionalCurvatureAt] using
        neg_le_sectionalCurvatureAt_of_hasCurvatureOperatorNormLeAt hK hRm
          (e 0) (e i)
    have hge : -((Module.finrank ℝ E : ℝ) - 1) * K ≤ ricciTensorAt g p u u := by
      have h := ricciForm_self_ge_of_sectionalCurvature_ge hB e 0 hKsec
      rw [he0, hform_eq u, Fintype.card_fin] at h
      convert h using 1
      ring
    have hscale : ricciTensorAt g p v v =
        nv ^ 2 * ricciTensorAt g p u u := by
      calc ricciTensorAt g p v v
          = ricciForm hB v v := (hform_eq v).symm
        _ = ricciForm hB (nv • u) (nv • u) := by rw [hv_eq]
        _ = nv * ricciForm hB u (nv • u) :=
          ricciForm_smul_left hB nv u (nv • u)
        _ = nv * (nv * ricciForm hB u u) := by
          rw [ricciForm_smul_right]
        _ = nv ^ 2 * ricciForm hB u u := by ring
        _ = nv ^ 2 * ricciTensorAt g p u u := by rw [hform_eq]
    have hmet : g.metricInner p v v = nv ^ 2 :=
      real_inner_self_eq_norm_sq v
    calc
      -((Module.finrank ℝ E : ℝ) - 1) * K * g.metricInner p v v
          = nv ^ 2 * (-((Module.finrank ℝ E : ℝ) - 1) * K) := by
            rw [hmet]; ring
      _ ≤ nv ^ 2 * ricciTensorAt g p u u :=
        mul_le_mul_of_nonneg_left hge (sq_nonneg _)
      _ = ricciTensorAt g p v v := hscale.symm
/- SWARM_PROOF_END -/

end MorganTianLib
