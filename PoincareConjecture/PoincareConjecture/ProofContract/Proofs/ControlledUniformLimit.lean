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
/-- Summable uniform step control produces a genuine continuous uniform limit. -/
theorem continuous_limit_of_summable_steps {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] [CompleteSpace Y]
    (f : ℕ → X → Y) (hf : ∀ n, Continuous (f n)) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hstep : ∀ n x, dist (f (n+1) x) (f n x) ≤ a n) :
    ∃ g : X → Y, Continuous g ∧ TendstoUniformly f g atTop :=
/- SWARM_PROOF_BEGIN -/
by
  have hcauchy : ∀ x, CauchySeq (fun n => f n x) := by
    intro x
    apply cauchySeq_of_summable_dist
    refine hs.of_nonneg_of_le (fun n => dist_nonneg) ?_
    intro n
    simpa [Nat.succ_eq_add_one, dist_comm] using hstep n x
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  have htail : Tendsto (fun n : ℕ => ∑' m : ℕ, a (n + m)) atTop (𝓝 0) := by
    have hpartial := hs.tendsto_sum_tsum_nat
    have htail_eq : ∀ n : ℕ, (∑' m : ℕ, a (n + m)) =
        (∑' m : ℕ, a m) - ∑ i ∈ Finset.range n, a i := by
      intro n
      rw [eq_sub_iff_add_eq]
      simpa [add_comm] using hs.sum_add_tsum_nat_add n
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => ∑' m : ℕ, a m) atTop (𝓝 (∑' m : ℕ, a m))).sub hpartial
    simpa only [sub_self] using h.congr' (Filter.Eventually.of_forall (fun n => (htail_eq n).symm))
  have htail_nonneg : ∀ n : ℕ, 0 ≤ ∑' m : ℕ, a (n + m) := by
    intro n
    exact tsum_nonneg (fun m => ha (n + m))
  have hunif : TendstoUniformly f g atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hε' : ∀ᶠ n : ℕ in atTop, (∑' m : ℕ, a (n + m)) < ε :=
      (tendsto_order.1 htail).2 _ hε
    have hε'' : ∀ᶠ n : ℕ in atTop,
        0 ≤ (∑' m : ℕ, a (n + m)) ∧ (∑' m : ℕ, a (n + m)) < ε :=
      (Filter.Eventually.of_forall htail_nonneg).and hε'
    filter_upwards [hε''] with n hn x
    have hdist : dist (f n x) (g x) < ε :=
      (dist_le_tsum_of_dist_le_of_tendsto a
      (fun k => by simpa [Nat.succ_eq_add_one, dist_comm] using hstep k x)
      hs (hg x) n).trans_lt hn.2
    simpa only [dist_comm] using hdist
  refine ⟨g, hunif.continuous (Filter.Frequently.of_forall hf), hunif⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
