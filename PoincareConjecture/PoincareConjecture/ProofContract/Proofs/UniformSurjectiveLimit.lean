import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.ControlledUniformLimit
import PoincareConjecture.ProofContract.Proofs.ControlledCollapseFibers
import PoincareConjecture.ProofContract.Proofs.SingleFiberQuotient
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology
/-- Surjectivity survives a uniform limit on a compact domain, without an inverse-limit hypothesis. -/
theorem uniform_limit_surjective_compact {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]
    (f : ℕ → X → Y) (q : X → Y) (hq : Continuous q)
    (hf : ∀ n, Surjective (f n)) (hlim : TendstoUniformly f q atTop) : Surjective q :=
/- SWARM_PROOF_BEGIN -/
by
  intro y
  have hy : y ∈ closure (range q) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hε' : ∀ᶠ n : ℕ in atTop, ∀ x, dist (q x) (f n x) < ε :=
      (Metric.tendstoUniformly_iff.mp hlim) ε hε
    obtain ⟨n, hn⟩ := eventually_atTop.1 hε'
    obtain ⟨x, hx⟩ := hf n y
    refine ⟨q x, ⟨x, rfl⟩, ?_⟩
    simpa [dist_comm, hx] using hn n le_rfl x
  exact (isCompact_range hq).isClosed.closure_subset hy
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
