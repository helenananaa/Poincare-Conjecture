import PoincareConjecture.ParallelImplementation.CoherentForcingGraphInverse
import PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ProjectedFullInverseBall
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
theorem exists_projected_full_inverse_ball
    {Y A : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [CompleteSpace A]
    (T alpha R : ℝ) (hR : 0 < R) (P : Y →L[ℝ] ForcingJet A T)
    (hP : ∀ z : Y, P z ∈ forcingGraph A T alpha) (hsmall : ‖P‖*R ≤ 1/2) :
    ∃ I : Y → ForcingJet A T,
      I 0 = (BoundedContinuousFunction.const (Slab T) 1,0) ∧
      (∀ z : Y, ‖z‖ ≤ R → I z ∈ forcingGraph A T alpha ∧ ‖I z‖ ≤ 2 ∧
        (∀ p : Slab T, (1-(P z).1 p)*(I z).1 p=1 ∧
          (I z).1 p*(1-(P z).1 p)=1)) ∧
      (∀ z w : Y, ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖I z-I w‖ ≤ (12*‖P‖)*‖z-w‖) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let R0 : ℝ := ‖P‖ * R
  have hR0 : 0 ≤ R0 := by
    dsimp [R0]
    positivity
  have hR0small : R0 ≤ 1 / 2 := by
    simpa [R0] using hsmall
  let S := {a : ForcingJet A T // a ∈ forcingGraph A T alpha ∧
    ‖a.1‖ ≤ (1 / 2 : ℝ) ∧ ‖a.2‖ ≤ R0}
  obtain ⟨J, hJspec, hJlip⟩ :=
    PoincareConjecture.ParallelImplementation.CoherentForcingGraphInverse.exists_coherent_forcing_graph_inverse
      (A := A) T alpha (1 / 2) R0 (by norm_num) (by norm_num) hR0
  let arg : (z : Y) → ‖z‖ ≤ R → S := fun z hz =>
    ⟨P z, hP z, (norm_fst_le (P z)).trans (by
      calc
        ‖P z‖ ≤ ‖P‖ * ‖z‖ := P.le_opNorm z
        _ ≤ R0 := by
          dsimp [R0]
          exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        _ ≤ 1 / 2 := hR0small),
      (norm_snd_le (P z)).trans (by
        calc
          ‖P z‖ ≤ ‖P‖ * ‖z‖ := P.le_opNorm z
          _ ≤ R0 := by
            dsimp [R0]
            exact mul_le_mul_of_nonneg_left hz (norm_nonneg _))⟩
  let oneJet : ForcingJet A T :=
    ((1 : Slab T →ᵇ A), (0 : Pair T →ᵇ A))
  have honeGraph : oneJet ∈ forcingGraph A T alpha := by
    intro p
    simp [oneJet]
  have hzeroBall : ‖(0 : Y)‖ ≤ R := by
    simpa using hR.le
  let a0 : S := arg 0 hzeroBall
  have hJ0value : ∀ p : Slab T, (J a0).1 p = 1 := by
    intro p
    have hid := (hJspec a0).2.1 p
    simpa [a0, arg, P.map_zero] using hid.1
  have hJ0eq : J a0 = oneJet :=
    PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha (J a0) oneJet (hJspec a0).1 honeGraph hJ0value
  let I : Y → ForcingJet A T := fun z =>
    if hz : ‖z‖ ≤ R then J (arg z hz) else oneJet
  have hIbranch (z : Y) (hz : ‖z‖ ≤ R) :
      I z = J (arg z hz) := by
    simp [I, hz]
  refine ⟨I, ?_, ?_, ?_⟩
  · rw [hIbranch 0 hzeroBall]
    exact hJ0eq
  · intro z hz
    rw [hIbranch z hz]
    refine ⟨(hJspec (arg z hz)).1, ?_, ?_⟩
    · have hbound := (hJspec (arg z hz)).2.2
      have hfour : 4 * R0 ≤ 2 := by nlinarith
      have hmax :
          max (1 / (1 - (1 / 2 : ℝ)))
            ((1 / (1 - (1 / 2 : ℝ))) ^ 2 * R0) ≤ 2 := by
        apply max_le
        · norm_num
        · rw [show (1 / (1 - (1 / 2 : ℝ))) ^ 2 = 4 by norm_num]
          exact hfour
      have hbound' : ‖J (arg z hz)‖ ≤
          max (1 / (1 - (1 / 2 : ℝ)))
            ((1 / (1 - (1 / 2 : ℝ))) ^ 2 * R0) := by
        simpa using hbound
      exact hbound'.trans hmax
    · intro p
      have hid := (hJspec (arg z hz)).2.1 p
      simpa [arg] using hid
  · intro z w hz hw
    rw [hIbranch z hz, hIbranch w hw]
    have hraw :
        ‖J (arg z hz)-J (arg w hw)‖ ≤
          (4 + 16 * R0) * ‖(arg z hz).1 - (arg w hw).1‖ := by
      have h := hJlip (arg z hz) (arg w hw)
      convert h using 1
      norm_num
    have hPdiff : ‖P z - P w‖ ≤ ‖P‖ * ‖z - w‖ := by
      simpa only [map_sub] using P.le_opNorm (z - w)
    have hcoeff : 4 + 16 * R0 ≤ 12 := by
      nlinarith
    calc
      ‖J (arg z hz)-J (arg w hw)‖ ≤
          (4 + 16 * R0) * ‖(arg z hz).1 - (arg w hw).1‖ := hraw
      _ = (4 + 16 * R0) * ‖P z - P w‖ := by rfl
      _ ≤ (4 + 16 * R0) * (‖P‖ * ‖z - w‖) :=
        mul_le_mul_of_nonneg_left hPdiff (by positivity)
      _ ≤ 12 * ‖P‖ * ‖z - w‖ := by
        have hnonneg : 0 ≤ ‖P‖ * ‖z - w‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        nlinarith
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ProjectedFullInverseBall
