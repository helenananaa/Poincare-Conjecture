import PoincareConjecture.ProofContract.Refinement20260927.CompactTubularData
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- **Math.** Reuse the exact pinned compact-neighborhood theorem, rather than
spending a worker on an already available result. -/
theorem checked_compact_injective_neighborhood : CompactInjectiveNeighborhoodStatement.{u} := by
  intro X inst n f K hf hK hinj hlocal
  exact hinj.exists_isOpen_superset hK (fun x _ => hf.continuousAt) (by
    intro x hx
    obtain ⟨U,hU,hxU,hi⟩ := hlocal x hx
    exact ⟨U,hU.mem_nhds hxU,hi⟩)
/-- **Math.** The specified embedding is retained in the retraction output. -/
theorem local_tubes_retraction_of_assembly (assemble : TubularInverseAssemblyStatement.{u})
    {N : CompactSmoothThree.{u}} {n : ℕ} {e : CompactEuclideanEmbedding N n}
    (T : LocalTubularData e) : ∃ R : SmoothRetractionData N n, R.embed = e.map :=
  local_tubular_data_to_retraction checked_compact_injective_neighborhood assemble T
#print axioms checked_compact_injective_neighborhood
#print axioms local_tubes_retraction_of_assembly
end PoincareConjecture.ProofContract.Refinement20260927
