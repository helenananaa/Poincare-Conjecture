import PoincareConjecture.ParallelImplementation.CoherentForcingGraphInverse
import PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ProjectedInverseCorrectionBall
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
theorem exists_projected_inverse_correction_ball
    {Y A : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [CompleteSpace A]
    (T alpha R : ℝ) (hR : 0 < R) (P : Y →L[ℝ] ForcingJet A T)
    (hP : ∀ z, P z ∈ forcingGraph A T alpha) (hsmall : ‖P‖*R ≤ 1/2) :
    ∃ J : Y → ForcingJet A T, J 0 = 0 ∧
      (∀ z, ‖z‖ ≤ R → J z ∈ forcingGraph A T alpha ∧
        (∀ p : Slab T,
          (1-(P z).1 p)*(1+(J z).1 p)=1 ∧
          (1+(J z).1 p)*(1-(P z).1 p)=1)) ∧
      (∀ z w, ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖J z-J w‖ ≤ (12*‖P‖)*‖z-w‖) :=
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
  obtain ⟨I, hIspec, hIlip⟩ :=
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
  have hI0value : ∀ p : Slab T, (I a0).1 p = 1 := by
    intro p
    have hid := (hIspec a0).2.1 p
    have hidleft := hid.1
    simpa [a0, arg, P.map_zero] using hidleft
  have hI0eq : I a0 = oneJet :=
    PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha (I a0) oneJet (hIspec a0).1 honeGraph hI0value
  let J : Y → ForcingJet A T := fun z =>
    if hz : ‖z‖ ≤ R then I (arg z hz) - oneJet else 0
  have hJbranch (z : Y) (hz : ‖z‖ ≤ R) :
      J z = I (arg z hz) - oneJet := by
    simp [J, hz]
  refine ⟨J, ?_, ?_, ?_⟩
  · rw [hJbranch 0 hzeroBall]
    change I a0 - oneJet = 0
    rw [hI0eq]
    exact sub_self _
  · intro z hz
    rw [hJbranch z hz]
    constructor
    · intro p
      change (I (arg z hz)).2 p - 0 =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((I (arg z hz)).1 p.1.1 - 1 - ((I (arg z hz)).1 p.1.2 - 1))
      rw [(hIspec (arg z hz)).1 p]
      abel
    · intro p
      have hid := (hIspec (arg z hz)).2.1 p
      constructor
      · simpa [oneJet] using hid.1
      · simpa [oneJet] using hid.2
  · intro z w hz hw
    rw [hJbranch z hz, hJbranch w hw]
    have hraw :
        ‖I (arg z hz) - I (arg w hw)‖ ≤
          (4 + 16 * R0) * ‖(arg z hz).1 - (arg w hw).1‖ := by
      have h := hIlip (arg z hz) (arg w hw)
      convert h using 1; norm_num
    have hPdiff : ‖P z - P w‖ ≤ ‖P‖ * ‖z - w‖ := by
      simpa only [map_sub] using P.le_opNorm (z - w)
    have hcoeff : 4 + 16 * R0 ≤ 12 := by
      nlinarith
    calc
      ‖(I (arg z hz) - oneJet) - (I (arg w hw) - oneJet)‖ =
          ‖I (arg z hz) - I (arg w hw)‖ := by
            congr 1
            abel
      _ ≤ (4 + 16 * R0) * ‖(arg z hz).1 - (arg w hw).1‖ := hraw
      _ = (4 + 16 * R0) * ‖P z - P w‖ := by rfl
      _ ≤ (4 + 16 * R0) * (‖P‖ * ‖z - w‖) :=
        mul_le_mul_of_nonneg_left hPdiff (by positivity)
      _ ≤ 12 * ‖P‖ * ‖z - w‖ := by
        have hnonneg : 0 ≤ ‖P‖ * ‖z - w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        nlinarith
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ProjectedInverseCorrectionBall
