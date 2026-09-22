import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.Proofs.ChartSupportedHomeomorph
import PoincareConjecture.ProofContract.Proofs.EuclideanBallCompression
import PoincareConjecture.ProofContract.Proofs.BufferedRadiusProfile
import PoincareConjecture.ProofContract.Proofs.RadialHomeomorphLift
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology
theorem uniform_limit_exact_fibers {X : Type u} {Y : Type v} [MetricSpace Y]
    (f : ℕ → X → Y) (q : X → Y) (K : Set X)
    (hf : TendstoUniformly f q atTop)
    (hsmall : ∀ n x y, x ∈ K → y ∈ K → dist (f n x) (f n y) ≤ (1/2:ℝ)^n)
    (hsep : ∀ x y, x ≠ y → ¬(x ∈ K ∧ y ∈ K) →
      ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n ≥ N, ε ≤ dist (f n x) (f n y)) :
    ∀ x y, q x = q y ↔ x=y ∨ (x ∈ K ∧ y ∈ K) :=
/- SWARM_PROOF_BEGIN -/
by
  intro x y
  constructor
  · intro hq
    by_cases hxy : x = y
    · exact Or.inl hxy
    by_contra hK
    have hnotboth : ¬(x ∈ K ∧ y ∈ K) := by
      intro h
      exact hK (Or.inr h)
    obtain ⟨ε, hε, N, hN⟩ := hsep x y hxy hnotboth
    have hdist : Tendsto (fun n => dist (f n x) (f n y)) atTop
        (𝓝 (dist (q x) (q y))) :=
      (hf.tendsto_at x).dist (hf.tendsto_at y)
    have hdist0 : Tendsto (fun n => dist (f n x) (f n y)) atTop (𝓝 0) := by
      simpa [hq] using hdist
    have hlt : ∀ᶠ n in atTop, dist (f n x) (f n y) < ε := by
      filter_upwards [Metric.tendsto_nhds.1 hdist0 ε hε] with n hn
      simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hn
    have hge : ∀ᶠ n in atTop, ε ≤ dist (f n x) (f n y) :=
      eventually_atTop.2 ⟨N, hN⟩
    obtain ⟨n, hnlt, hnge⟩ := (hlt.and hge).exists
    exact (not_lt_of_ge hnge) hnlt
  · intro hxy
    rcases hxy with rfl | ⟨hx, hy⟩
    · rfl
    have hdist : Tendsto (fun n => dist (f n x) (f n y)) atTop
        (𝓝 (dist (q x) (q y))) :=
      (hf.tendsto_at x).dist (hf.tendsto_at y)
    have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hzero : Tendsto (fun n => dist (f n x) (f n y)) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun n => hsmall n x y hx hy) hpow
    have hqdist : dist (q x) (q y) = 0 := tendsto_nhds_unique hdist hzero
    exact dist_eq_zero.mp hqdist
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
