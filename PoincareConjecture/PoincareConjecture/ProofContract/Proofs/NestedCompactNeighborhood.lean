import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.Proofs.ChartSupportedHomeomorph
import PoincareConjecture.ProofContract.Proofs.EuclideanBallCompression
import PoincareConjecture.ProofContract.Proofs.CoordinateBallShrinking
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology
/-- Nested compact sets eventually lie in every open neighborhood of their full intersection. -/
theorem nested_compact_eventually_in_neighborhood {X : Type u} [TopologicalSpace X] [T2Space X]
    (K : ℕ → Set X) (hc : ∀ n, IsCompact (K n)) (hn : Antitone K)
    (U : Set X) (hU : IsOpen U) (hKU : (⋂ n, K n) ⊆ U) : ∃ n, K n ⊆ U :=
/- SWARM_PROOF_BEGIN -/
by
  by_contra h
  push Not at h
  have hnon : ∀ n, (K n ∩ Uᶜ).Nonempty := fun n =>
    Set.inter_compl_nonempty_iff.mpr (h n)
  have hdir : Directed (· ⊇ ·) (fun n => K n ∩ Uᶜ) := by
    intro i j
    rcases hn.directed_ge i j with ⟨k, hki, hkj⟩
    exact ⟨k, inter_subset_inter hki subset_rfl, inter_subset_inter hkj subset_rfl⟩
  have hinter : (⋂ n, K n ∩ Uᶜ).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun n => K n ∩ Uᶜ) hdir hnon
      (fun n => (hc n).inter_right hU.isClosed_compl)
      (fun n => (hc n).isClosed.inter hU.isClosed_compl)
  have hfull : ((⋂ n, K n) ∩ Uᶜ).Nonempty := by
    simpa [← iInter_inter] using hinter
  rcases hfull with ⟨x, hxK, hxU⟩
  exact hxU (hKU hxK)
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
