import PoincareConjecture.ParallelImplementation.ProjectedFullInverseBall
import PoincareConjecture.ParallelImplementation.ForcingGraphQuadrilinearLift
import PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.AffineForcingGraphInverse
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
theorem exists_affine_forcing_graph_inverse
    {Y A : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [CompleteSpace A]
    (T alpha R : ℝ) (hR : 0 < R) (a : ForcingJet A T) (ha : a ∈ forcingGraph A T alpha)
    (P : Y →L[ℝ] ForcingJet A T) (hP : ∀ z : Y, P z ∈ forcingGraph A T alpha)
    (hsmall : ‖a‖+‖P‖*R ≤ 1/2) :

    ∃ I : Y → ForcingJet A T,
      (∀ z : Y, ‖z‖ ≤ R → I z ∈ forcingGraph A T alpha ∧ ‖I z‖ ≤ 2 ∧
        ∀ p : Slab T, (1-(a+P z).1 p)*(I z).1 p=1 ∧ (I z).1 p*(1-(a+P z).1 p)=1) ∧
      (∀ p : Slab T, (I 0).1 p=Ring.inverse (1-a.1 p)) ∧
      ∀ z w : Y, ‖z‖ ≤ R → ‖w‖ ≤ R → ‖I z-I w‖ ≤ (12*‖P‖)*‖z-w‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let S := {x : ForcingJet A T // x ∈ forcingGraph A T alpha ∧
    ‖x.1‖ ≤ (1 / 2 : ℝ) ∧ ‖x.2‖ ≤ (1 / 2 : ℝ)}
  obtain ⟨J, hJspec, hJlip⟩ :=
    PoincareConjecture.ParallelImplementation.CoherentForcingGraphInverse.exists_coherent_forcing_graph_inverse
      (A := A) T alpha (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hAffineGraph (z : Y) : a + P z ∈ forcingGraph A T alpha := by
    intro p
    change a.2 p + (P z).2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (a.1 p.1.1 + (P z).1 p.1.1 - (a.1 p.1.2 + (P z).1 p.1.2))
    rw [ha p, hP z p]
    simp [sub_eq_add_neg, smul_add]
    abel
  have hAffineNorm (z : Y) (hz : ‖z‖ ≤ R) : ‖a + P z‖ ≤ 1 / 2 := by
    calc
      ‖a + P z‖ ≤ ‖a‖ + ‖P z‖ := norm_add_le _ _
      _ ≤ ‖P‖ * ‖z‖ + ‖a‖ := by
        calc
          ‖a‖ + ‖P z‖ = ‖P z‖ + ‖a‖ := by ring
          _ ≤ ‖P‖ * ‖z‖ + ‖a‖ := add_le_add_left (P.le_opNorm z) ‖a‖
      _ = ‖a‖ + ‖P‖ * ‖z‖ := by ring
      _ ≤ ‖P‖ * R + ‖a‖ := by
        calc
          ‖a‖ + ‖P‖ * ‖z‖ = ‖P‖ * ‖z‖ + ‖a‖ := by ring
          _ ≤ ‖P‖ * R + ‖a‖ :=
            add_le_add_left (mul_le_mul_of_nonneg_left hz (norm_nonneg P)) ‖a‖
      _ = ‖a‖ + ‖P‖ * R := by ring
      _ ≤ 1 / 2 := hsmall
  let arg : (z : Y) → ‖z‖ ≤ R → S := fun z hz =>
    ⟨a + P z, hAffineGraph z,
      (norm_fst_le (a + P z)).trans (hAffineNorm z hz),
      (norm_snd_le (a + P z)).trans (hAffineNorm z hz)⟩
  have hzeroBall : ‖(0 : Y)‖ ≤ R := by
    simpa using hR.le
  let a0 : S := arg 0 hzeroBall
  have hIzeroInput : a0.1 = a := by
    simp [a0, arg, P.map_zero]
  let I : Y → ForcingJet A T := fun z =>
    if hz : ‖z‖ ≤ R then J (arg z hz) else 0
  have hIbranch (z : Y) (hz : ‖z‖ ≤ R) : I z = J (arg z hz) := by
    simp [I, hz]
  have hcanonical (p : Slab T) : (J a0).1 p = Ring.inverse (1 - a.1 p) := by
    have hinv := (hJspec a0).2.1 p
    have hleft : (1 - a.1 p) * (J a0).1 p = 1 := by
      simpa [a0, arg, P.map_zero] using hinv.1
    have hright : (J a0).1 p * (1 - a.1 p) = 1 := by
      simpa [a0, arg, P.map_zero] using hinv.2
    have hu : IsUnit (1 - a.1 p) := by
      exact ⟨⟨1 - a.1 p, (J a0).1 p, hleft, hright⟩, rfl⟩
    calc
      (J a0).1 p = (J a0).1 p * ((1 - a.1 p) * Ring.inverse (1 - a.1 p)) := by
        rw [Ring.mul_inverse_cancel (1 - a.1 p) hu, mul_one]
      _ = ((J a0).1 p * (1 - a.1 p)) * Ring.inverse (1 - a.1 p) := by
        rw [mul_assoc]
      _ = Ring.inverse (1 - a.1 p) := by rw [hright, one_mul]
  refine ⟨I, ?_, ?_, ?_⟩
  · intro z hz
    rw [hIbranch z hz]
    refine ⟨(hJspec (arg z hz)).1, ?_, ?_⟩
    · have hbound := (hJspec (arg z hz)).2.2
      have hmax :
          max (1 / (1 - (1 / 2 : ℝ)))
            ((1 / (1 - (1 / 2 : ℝ))) ^ 2 * (1 / 2 : ℝ)) ≤ 2 := by
        norm_num
      exact hbound.trans hmax
    · intro p
      exact (hJspec (arg z hz)).2.1 p
  · intro p
    rw [hIbranch 0 hzeroBall]
    exact hcanonical p
  · intro z w hz hw
    rw [hIbranch z hz, hIbranch w hw]
    have hargDiff : (arg z hz).1 - (arg w hw).1 = P z - P w := by
      change (a + P z) - (a + P w) = P z - P w
      abel
    have hJbound :
        ‖J (arg z hz) - J (arg w hw)‖ ≤
          12 * ‖(arg z hz).1 - (arg w hw).1‖ := by
      have hh := hJlip (arg z hz) (arg w hw)
      convert hh using 1; norm_num
    have hPdiff : ‖P z - P w‖ ≤ ‖P‖ * ‖z - w‖ := by
      calc
        ‖P z - P w‖ = ‖P (z - w)‖ := by rw [map_sub]
        _ ≤ ‖P‖ * ‖z - w‖ := P.le_opNorm _
    calc
      ‖J (arg z hz) - J (arg w hw)‖ ≤
          12 * ‖P z - P w‖ := by rw [← hargDiff]; exact hJbound
      _ ≤ 12 * (‖P‖ * ‖z - w‖) :=
        mul_le_mul_of_nonneg_left hPdiff (by norm_num)
      _ = (12 * ‖P‖) * ‖z - w‖ := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.AffineForcingGraphInverse
