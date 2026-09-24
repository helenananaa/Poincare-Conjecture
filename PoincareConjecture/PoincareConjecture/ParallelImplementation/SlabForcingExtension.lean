import PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SlabForcingExtension
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Time clamping extends actual slab data without loss of supremum norm or parabolic Holder bound. -/
theorem slab_forcing_extension
    {V : Type*} [NormedAddCommGroup V]
    (T alpha H : ℝ) (hT : 0 ≤ T) (ha : 0 < alpha) (hH : 0 ≤ H)
    (F : Slab T →ᵇ V)
    (hholder : ∀ p q : Slab T, ‖F p-F q‖ ≤ H*parabolicRho p q ^ alpha) :
    ∃ G : (ℝ × E3) →ᵇ V,
      (∀ t : Set.Icc (0:ℝ) T, ∀ x : E3, G ((t:ℝ),x) = F (t,x)) ∧
      ‖G‖ = ‖F‖ ∧ ∀ p q : ℝ × E3,
        ‖G p-G q‖ ≤ H*(‖p.2-q.2‖ + Real.sqrt |p.1-q.1|)^alpha :=
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
  let G : (ℝ × E3) →ᵇ V := F.compContinuous retract
  refine ⟨G, ?_, ?_, ?_⟩
  · intro t x
    change F (clamp (t : ℝ), x) = F (t, x)
    congr 1
    exact Prod.ext (Set.projIcc_val hT t) rfl
  · apply le_antisymm
    · apply (BoundedContinuousFunction.norm_le (f := G) (norm_nonneg _)).2
      intro p
      change ‖F (retract p)‖ ≤ ‖F‖
      exact F.norm_coe_le_norm (retract p)
    · apply (BoundedContinuousFunction.norm_le (f := F) (norm_nonneg _)).2
      intro p
      have heval : G ((p.1 : ℝ), p.2) = F p := by
        change F (clamp (p.1 : ℝ), p.2) = F p
        congr 1
        exact Prod.ext (Set.projIcc_val hT p.1) rfl
      rw [← heval]
      exact G.norm_coe_le_norm ((p.1 : ℝ), p.2)
  · intro p q
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
end PoincareConjecture.ParallelImplementation.SlabForcingExtension
