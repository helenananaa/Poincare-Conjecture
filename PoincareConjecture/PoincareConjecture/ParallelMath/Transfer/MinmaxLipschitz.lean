import PoincareConjecture.ParallelMath.Variational.MinmaxTransfer
import PoincareConjecture.ParallelMath.Variational.InfimumAdditive
import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Uniform parameterwise Lipschitz control gives a Lipschitz minmax value without attaining either extremum. -/
theorem leastPeak_lipschitz {T A B : Type*} [PseudoMetricSpace T] [Nonempty A] [Nonempty B]
    (F : T → A → B → ℝ) (hn : ∀ t a b, 0 ≤ F t a b)
    (hb : ∀ t a, BddAbove (range (F t a))) (K : NNReal)
    (hL : ∀ a b, LipschitzWith K (fun t => F t a b)) :
    LipschitzWith K (fun t => Variational.leastPeak (F t)) :=
/- SWARM_PROOF_BEGIN -/
by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  have hδ : 0 ≤ (K : ℝ) * dist s t := mul_nonneg K.coe_nonneg dist_nonneg
  have hnn : ∀ (u : T) (a : A), 0 ≤ Variational.peakCost (F u a) := fun u a => by
    obtain ⟨b⟩ := ‹Nonempty B›
    exact (hn u a b).trans (le_csSup (hb u a) (mem_range_self b))
  have hpeak : ∀ (u v : T) (a : A),
      Variational.peakCost (F u a) ≤
        Variational.peakCost (F v a) + (K : ℝ) * dist u v := by
    intro u v a
    simpa using
      Variational.peakCost_transport (F v a) (F u a) (hb v a) (hb u a)
        (id : B → B) surjective_id (1 : ℝ) ((K : ℝ) * dist u v) zero_le_one
        fun b => by
          have hdist := (hL a b).dist_le_mul u v
          rw [Real.dist_eq] at hdist
          have hpt := (sub_le_iff_le_add').mp (abs_le.mp hdist).2
          simpa [id, one_mul] using hpt
  have hclose : ∀ a,
      |Variational.peakCost (F s a) - Variational.peakCost (F t a)| ≤
        (K : ℝ) * dist s t := by
    intro a
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hts := hpeak t s a
      rw [dist_comm t s] at hts
      linarith
    · exact (sub_le_iff_le_add).mpr (by linarith [hpeak s t a])
  simpa [Variational.leastPeak, Real.dist_eq] using
    Variational.leastCost_uniform_perturbation
      (fun a => Variational.peakCost (F s a))
      (fun a => Variational.peakCost (F t a))
      (hnn s) (hnn t) ((K : ℝ) * dist s t) hδ hclose
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
