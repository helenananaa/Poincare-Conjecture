import Mathlib

open scoped BigOperators

namespace PoincareConjecture.CriticalPath.SurgeryBudget

/-- A real-valued uniform cardinality bound on all finite samples proves actual finiteness.
In particular the hypothesis does not presuppose local finiteness of event times. -/
theorem finite_of_uniform_finite_subset_real_bound
    {X : Type*} (S : Set X) (B : ℝ)
    (hbound : ∀ s : Finset X, (↑s : Set X) ⊆ S → (s.card : ℝ) ≤ B) :
    S.Finite ∧ (S.ncard : ℝ) ≤ B := by
/- SWARM_PROOF_BEGIN -/
  classical
  have hfinite : S.Finite := by
    by_contra hS
    have hInf : S.Infinite := hS
    obtain ⟨n, hn⟩ := exists_nat_gt B
    obtain ⟨s, hsS, hs_card⟩ := hInf.exists_subset_card_eq n
    have hs_bound := hbound s hsS
    rw [hs_card] at hs_bound
    linarith
  refine ⟨hfinite, ?_⟩
  have hs_bound := hbound hfinite.toFinset (by
    intro x hx
    exact hfinite.mem_toFinset.mp hx)
  simpa [Set.ncard_eq_toFinset_card S hfinite] using hs_bound
/- SWARM_PROOF_END -/

end PoincareConjecture.CriticalPath.SurgeryBudget
