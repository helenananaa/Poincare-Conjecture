import PoincareConjecture.ParallelImplementation.ForcingGraphScalarProduct
import PoincareConjecture.ParallelImplementation.FullJetHessianComponent
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoefficientHessianMultiplierModular
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Actual variable-coefficient Hessian contraction on value and Holder-increment fields. -/
theorem exists_coefficient_hessian_multiplier_modular (T alpha : ℝ) (hT : 0 ≤ T)
    (A : Fin 3 → Fin 3 → ForcingJet ℝ T)
    (hA : ∀ i j, A i j ∈ forcingGraph ℝ T alpha) :
    ∃ R : FullJet T →L[ℝ] ForcingJet E6 T,
      ‖R‖ ≤ 2 * (∑ i : Fin 3, ∑ j : Fin 3, ‖A i j‖) ∧
      (∀ z p, (R z).1 p = ∑ i : Fin 3, ∑ j : Fin 3,
        (A i j).1 p • z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      (∀ z p, (R z).2 p = ∑ i : Fin 3, ∑ j : Fin 3,
        ((A i j).1 p.1.1 • z.1.1.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
         (A i j).2 p • z.1.1.1.2.2 p.1.2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) ∧
      ∀ z ∈ fullParabolicJetSet T alpha hT, R z ∈ forcingGraph E6 T alpha :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let mWitness (i j : Fin 3) :=
    PoincareConjecture.ParallelImplementation.ForcingGraphScalarProduct.exists_forcing_scalar_product
      (V := E6) (T := T) (alpha := alpha) (A i j) (hA i j)
  let hWitness (i j : Fin 3) :=
    PoincareConjecture.ParallelImplementation.FullJetHessianComponent.exists_full_jet_hessian_component
      (T := T) (alpha := alpha) hT i j
  let M (i j : Fin 3) : ForcingJet E6 T →L[ℝ] ForcingJet E6 T :=
    Classical.choose (mWitness i j)
  let H (i j : Fin 3) : FullJet T →L[ℝ] ForcingJet E6 T :=
    Classical.choose (hWitness i j)
  have hMdata (i j : Fin 3) := Classical.choose_spec (mWitness i j)
  have hHdata (i j : Fin 3) := Classical.choose_spec (hWitness i j)
  have hMnorm (i j : Fin 3) : ‖M i j‖ ≤ 2 * ‖A i j‖ := (hMdata i j).1
  have hMvalue (i j : Fin 3) (w : ForcingJet E6 T) (p : Slab T) :
      ((M i j) w).1 p = (A i j).1 p • w.1 p := (hMdata i j).2.1 w p
  have hMincrement (i j : Fin 3) (w : ForcingJet E6 T) (p : Pair T) :
      ((M i j) w).2 p = (A i j).1 p.1.1 • w.2 p + (A i j).2 p • w.1 p.1.2 :=
    (hMdata i j).2.2.1 w p
  have hMgraph (i j : Fin 3) (w : ForcingJet E6 T)
      (hw : w ∈ forcingGraph E6 T alpha) :
      M i j w ∈ forcingGraph E6 T alpha := (hMdata i j).2.2.2 w hw
  have hHnorm (i j : Fin 3) : ‖H i j‖ ≤ 1 := (hHdata i j).1
  have hHvalue (i j : Fin 3) (z : FullJet T) (p : Slab T) :
      (H i j z).1 p = z.1.1.1.2.2 p
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
    (hHdata i j).2.1 z p
  have hHincr (i j : Fin 3) (z : FullJet T) (p : Pair T) :
      (H i j z).2 p = z.1.1.2 p
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
    (hHdata i j).2.2.1 z p
  have hHgraph (i j : Fin 3) (z : FullJet T)
      (hz : z ∈ fullParabolicJetSet T alpha hT) :
      H i j z ∈ forcingGraph E6 T alpha := (hHdata i j).2.2.2 z hz
  let C (i j : Fin 3) : FullJet T →L[ℝ] ForcingJet E6 T := (M i j).comp (H i j)
  let R : FullJet T →L[ℝ] ForcingJet E6 T :=
    ∑ i : Fin 3, ∑ j : Fin 3, C i j
  have htermNorm (i j : Fin 3) :
      ‖C i j‖ ≤ 2 * ‖A i j‖ := by
    calc
      ‖C i j‖ ≤ ‖M i j‖ * ‖H i j‖ := (M i j).opNorm_comp_le (H i j)
      _ ≤ (2 * ‖A i j‖) * 1 :=
        mul_le_mul (hMnorm i j) (hHnorm i j) (norm_nonneg (H i j)) (by norm_num)
      _ = 2 * ‖A i j‖ := by ring
  have hinnerNorm (i : Fin 3) :
      ‖∑ j : Fin 3, C i j‖ ≤ ∑ j : Fin 3, ‖C i j‖ := by
    exact norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => C i j)
  have houterNorm :
      ‖∑ i : Fin 3, ∑ j : Fin 3, C i j‖ ≤
        ∑ i : Fin 3, ‖∑ j : Fin 3, C i j‖ := by
    exact norm_sum_le (Finset.univ : Finset (Fin 3))
      (fun i => ∑ j : Fin 3, C i j)
  have hRnorm : ‖R‖ ≤ 2 * (∑ i : Fin 3, ∑ j : Fin 3, ‖A i j‖) := by
    calc
      ‖R‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖C i j‖ := by
        change ‖∑ i : Fin 3, ∑ j : Fin 3, C i j‖ ≤ _
        exact houterNorm.trans (Finset.sum_le_sum (fun i _ => hinnerNorm i))
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, 2 * ‖A i j‖ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact htermNorm i j
      _ = 2 * (∑ i : Fin 3, ∑ j : Fin 3, ‖A i j‖) := by
        simp only [Finset.mul_sum]
  let G : Submodule ℝ (ForcingJet E6 T) := {
    carrier := forcingGraph E6 T alpha
    zero_mem' := by
      intro p
      simp
    add_mem' := by
      intro x y hx hy p
      change x.2 p + y.2 p =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((x.1 + y.1) p.1.1 - (x.1 + y.1) p.1.2)
      rw [hx p, hy p]
      simp [sub_eq_add_neg, smul_add]
      abel
    smul_mem' := by
      intro c x hx p
      change c • x.2 p =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((c • x.1) p.1.1 - (c • x.1) p.1.2)
      rw [hx p]
      simp [smul_sub, smul_smul, mul_comm]
  }
  refine ⟨R, hRnorm, ?_, ?_, ?_⟩
  · intro z p
    simp [R, C, Prod.fst_sum, hMvalue, hHvalue]
  · intro z p
    simp [R, C, Prod.snd_sum, hMincrement, hHvalue, hHincr]
  · intro z hz
    change R z ∈ G
    have hterm (i j : Fin 3) : C i j z ∈ G := by
      exact hMgraph i j (H i j z) (hHgraph i j z hz)
    change (∑ i : Fin 3, ∑ j : Fin 3, C i j z) ∈ G
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro j hj
    exact hterm i j
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoefficientHessianMultiplierModular