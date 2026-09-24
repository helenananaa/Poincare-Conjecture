import PoincareConjecture.ParallelImplementation.UniformNearIdentityInverse
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingGraphNearIdentityInverse
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
 theorem exists_forcing_graph_near_identity_inverse
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [CompleteSpace A]
    (T alpha q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1)
    (a : ForcingJet A T) (ha : a ∈ forcingGraph A T alpha)
    (haq : ‖a.1‖ ≤ q) :
    ∃ b : ForcingJet A T, b ∈ forcingGraph A T alpha ∧
      (∀ p : Slab T, (1-a.1 p)*b.1 p = 1 ∧ b.1 p*(1-a.1 p) = 1) ∧
      (∀ p : Pair T, b.2 p = b.1 p.1.1 * a.2 p * b.1 p.1.2) ∧
      ‖b.1‖ ≤ 1/(1-q) ∧ ‖b.2‖ ≤ (1/(1-q))^2*‖a.2‖ ∧
      ‖b‖ ≤ max (1/(1-q)) ((1/(1-q))^2*‖a.2‖) :=
/- SWARM_PROOF_BEGIN -/
by
  have haPoint (p : Slab T) : ‖a.1 p‖ ≤ q :=
    (a.1.norm_coe_le_norm p).trans haq
  obtain ⟨inv, hinv, hinvBound, hresolvent, hinvDiff⟩ :=
    PoincareConjecture.ParallelImplementation.UniformNearIdentityInverse.exists_uniform_near_identity_inverse
      a.1 q hq0 hq haPoint
  let C : ℝ := 1 / (1 - q)
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCnonneg : 0 ≤ C := hCpos.le
  have hC2pos : 0 < C ^ 2 := sq_pos_of_pos hCpos
  have hinvContinuous : Continuous inv := by
    rw [Metric.continuous_iff]
    intro p ε hε
    obtain ⟨δ, hδ, hδa⟩ :=
      (Metric.continuous_iff.mp a.1.continuous) p (ε / C ^ 2)
        (div_pos hε hC2pos)
    refine ⟨δ, hδ, ?_⟩
    intro r hr
    have harg : ‖a.1 r - a.1 p‖ < ε / C ^ 2 := by
      simpa only [dist_eq_norm] using hδa r hr
    have hval := hinvDiff r p
    have hval' : ‖inv r - inv p‖ < ε := by
      calc
        ‖inv r - inv p‖ ≤ C ^ 2 * ‖a.1 r - a.1 p‖ := by
          simpa [C] using hval
        _ < C ^ 2 * (ε / C ^ 2) := mul_lt_mul_of_pos_left harg hC2pos
        _ = ε := by field_simp
    simpa only [dist_eq_norm] using hval'
  have hinvPointBound (p : Slab T) : ‖inv p‖ ≤ C := by
    simpa [C] using hinvBound p
  let invValues :=
    BoundedContinuousFunction.ofNormedAddCommGroup inv hinvContinuous C hinvPointBound
  have hinvValuesNorm : ‖invValues‖ ≤ C := by
    change ‖BoundedContinuousFunction.ofNormedAddCommGroup
      inv hinvContinuous C hinvPointBound‖ ≤ C
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      hinvContinuous hCnonneg hinvPointBound
  have hpair : Continuous (fun p : Pair T => (p.1 : Slab T × Slab T)) :=
    continuous_subtype_val
  have hleft : Continuous (fun p : Pair T => p.1.1) := continuous_fst.comp hpair
  have hright : Continuous (fun p : Pair T => p.1.2) := continuous_snd.comp hpair
  let incrementRaw : Pair T → A := fun p =>
    invValues p.1.1 * a.2 p * invValues p.1.2
  have hincrementContinuous : Continuous incrementRaw := by
    dsimp [incrementRaw]
    exact continuous_mul.comp
      ((continuous_mul.comp
        ((invValues.continuous.comp hleft).prodMk a.2.continuous)).prodMk
          (invValues.continuous.comp hright))
  have hincrementPointBound (p : Pair T) :
      ‖incrementRaw p‖ ≤ C ^ 2 * ‖a.2‖ := by
    dsimp [incrementRaw]
    calc
      ‖invValues p.1.1 * a.2 p * invValues p.1.2‖ ≤
          ‖invValues p.1.1 * a.2 p‖ * ‖invValues p.1.2‖ := norm_mul_le _ _
      _ ≤ (‖invValues p.1.1‖ * ‖a.2 p‖) * ‖invValues p.1.2‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (C * ‖a.2‖) * C := by
        gcongr
        · exact hinvPointBound _
        · exact a.2.norm_coe_le_norm p
        · exact hinvPointBound _
      _ = C ^ 2 * ‖a.2‖ := by ring
  let increments :=
    BoundedContinuousFunction.ofNormedAddCommGroup incrementRaw hincrementContinuous
      (C ^ 2 * ‖a.2‖) hincrementPointBound
  have hincrementsNorm : ‖increments‖ ≤ C ^ 2 * ‖a.2‖ := by
    change ‖BoundedContinuousFunction.ofNormedAddCommGroup incrementRaw
      hincrementContinuous (C ^ 2 * ‖a.2‖) hincrementPointBound‖ ≤ _
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      hincrementContinuous (mul_nonneg (sq_nonneg C) (norm_nonneg _))
        hincrementPointBound
  have hincrementGraph (p : Pair T) :
      incrementRaw p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (inv p.1.1 - inv p.1.2) := by
    have haGraph := ha p
    change a.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
      (a.1 p.1.1 - a.1 p.1.2) at haGraph
    calc
      incrementRaw p =
          invValues p.1.1 *
            ((parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
              (a.1 p.1.1 - a.1 p.1.2)) * invValues p.1.2 := by
        simp only [incrementRaw, haGraph]
      _ = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          (invValues p.1.1 * (a.1 p.1.1 - a.1 p.1.2) * invValues p.1.2) := by
        rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      _ = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          (inv p.1.1 - inv p.1.2) := by
        rw [hresolvent]
        congr 1
  have hbGraph : (invValues, increments) ∈ forcingGraph A T alpha := by
    intro p
    change increments p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
      (invValues p.1.1 - invValues p.1.2)
    change incrementRaw p = _
    exact hincrementGraph p
  refine ⟨(invValues, increments), hbGraph, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact hinv p
  · intro p
    change increments p = invValues p.1.1 * a.2 p * invValues p.1.2
    rfl
  · exact hinvValuesNorm
  · exact hincrementsNorm
  · simpa [C] using max_le_max hinvValuesNorm hincrementsNorm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingGraphNearIdentityInverse
