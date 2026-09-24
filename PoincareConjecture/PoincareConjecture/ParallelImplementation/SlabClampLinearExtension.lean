import PoincareConjecture.ParallelImplementation.SlabForcingExtension
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SlabClampLinearExtension
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- A fixed linear time-clamping extension preserves supremum norm and Holder control. -/
theorem exists_slab_clamp_linear_extension
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ E : (Slab T →ᵇ V) →L[ℝ] ((ℝ × E3) →ᵇ V), ‖E‖ ≤ 1 ∧
      (∀ F p, E F p = F (Set.projIcc 0 T hT p.1, p.2)) ∧
      (∀ F, ‖E F‖ = ‖F‖) ∧
      ∀ (alpha H : ℝ), 0 < alpha → 0 ≤ H → ∀ F : Slab T →ᵇ V,
        (∀ p q, ‖F p-F q‖ ≤ H*parabolicRho p q ^ alpha) →
        ∀ p q : ℝ × E3, ‖E F p-E F q‖ ≤
          H*(‖p.2-q.2‖ + Real.sqrt |p.1-q.1|)^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  let clamp : ℝ → Set.Icc (0 : ℝ) T := Set.projIcc 0 T hT
  have hclamp_cont : Continuous clamp := by
    dsimp [clamp]
    exact continuous_projIcc
  have hclamp_lipschitz (s t : ℝ) :
      |(clamp s : ℝ) - (clamp t : ℝ)| ≤ |s - t| := by
    dsimp [clamp]
    exact Set.abs_projIcc_sub_projIcc hT
  let retract : C(ℝ × E3, Slab T) :=
    ⟨fun p => (clamp p.1, p.2),
      (hclamp_cont.comp continuous_fst).prodMk continuous_snd⟩
  let L : (Slab T →ᵇ V) →ₗ[ℝ] ((ℝ × E3) →ᵇ V) :=
    { toFun := fun (F : Slab T →ᵇ V) =>
        BoundedContinuousFunction.compContinuous F retract
      map_add' := by
        intro F G
        ext p
        rfl
      map_smul' := by
        intro c F
        ext p
        simp }
  have hL_bound (F : Slab T →ᵇ V) : ‖L F‖ ≤ 1 * ‖F‖ := by
    have hnorm : ‖L F‖ ≤ ‖F‖ := by
      apply (BoundedContinuousFunction.norm_le (f := L F) (norm_nonneg _)).2
      intro p
      change ‖F (retract p)‖ ≤ ‖F‖
      exact F.norm_coe_le_norm (retract p)
    simpa using hnorm
  let E : (Slab T →ᵇ V) →L[ℝ] ((ℝ × E3) →ᵇ V) :=
    L.mkContinuous 1 hL_bound
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · exact LinearMap.mkContinuous_norm_le L zero_le_one hL_bound
  · intro F p
    change F (retract p) = F (clamp p.1, p.2)
    rfl
  · intro F
    apply le_antisymm
    · apply (BoundedContinuousFunction.norm_le (f := E F) (norm_nonneg _)).2
      intro p
      change ‖F (retract p)‖ ≤ ‖F‖
      exact F.norm_coe_le_norm (retract p)
    · apply (BoundedContinuousFunction.norm_le (f := F) (norm_nonneg _)).2
      intro p
      have heval : E F ((p.1 : ℝ), p.2) = F p := by
        change F (clamp (p.1 : ℝ), p.2) = F p
        congr 1
        exact Prod.ext (Set.projIcc_val hT p.1) rfl
      rw [← heval]
      exact (E F).norm_coe_le_norm ((p.1 : ℝ), p.2)
  · intro alpha H ha hH F hholder p q
    change ‖F (retract p) - F (retract q)‖ ≤
      H * (‖p.2 - q.2‖ + Real.sqrt |p.1 - q.1|) ^ alpha
    have htime :
        |((retract p).1 : ℝ) - ((retract q).1 : ℝ)| ≤ |p.1 - q.1| := by
      dsimp [retract]
      exact hclamp_lipschitz p.1 q.1
    have hrho : parabolicRho (retract p) (retract q) ≤
        ‖p.2 - q.2‖ + Real.sqrt |p.1 - q.1| := by
      unfold parabolicRho
      dsimp [retract]
      exact add_le_add (by rfl) (Real.sqrt_le_sqrt htime)
    have hrho_nonneg : 0 ≤ parabolicRho (retract p) (retract q) := by
      unfold parabolicRho
      positivity
    calc
      ‖F (retract p) - F (retract q)‖ ≤
          H * parabolicRho (retract p) (retract q) ^ alpha := hholder _ _
      _ ≤ H * (‖p.2 - q.2‖ + Real.sqrt |p.1 - q.1|) ^ alpha :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hrho_nonneg hrho ha.le) hH
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SlabClampLinearExtension
