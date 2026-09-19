import PoincareConjecture.ParallelMath.Transfer.HomotopyLeftInverse
import PoincareConjecture.ParallelMath.Variational.AdmissibleTransfer
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function
open scoped Manifold ContDiff
/-- A C1 comparison map with a left homotopy inverse transports actual C1 non-null maps and their least costs. -/
theorem c1_nonNull_leastCost_transport
    {ES EM EN : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HS HM HN : Type*} [TopologicalSpace HS] [TopologicalSpace HM] [TopologicalSpace HN]
    (IS : ModelWithCorners ℝ ES HS) (IM : ModelWithCorners ℝ EM HM) (IN : ModelWithCorners ℝ EN HN)
    {S M N : Type*} [TopologicalSpace S] [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace HS S] [ChartedSpace HM M] [ChartedSpace HN N]
    [Nonempty {f : C(S,M) // ContMDiff IS IM 1 f ∧ NonNull f}]
    (p : C(M,N)) (r : C(N,M)) (hp : ContMDiff IM IN 1 p)
    (hr : (r.comp p).Homotopic (ContinuousMap.id M))
    (A : C(S,M) → ℝ) (B : C(S,N) → ℝ)
    (hA : ∀ f : {f : C(S,M) // ContMDiff IS IM 1 f ∧ NonNull f}, 0 ≤ A f.1)
    (hB : ∀ f : {f : C(S,N) // ContMDiff IS IN 1 f ∧ NonNull f}, 0 ≤ B f.1)
    (L δ : ℝ) (hL : 0 ≤ L)
    (hb : ∀ f : {f : C(S,M) // ContMDiff IS IM 1 f ∧ NonNull f},
      B (p.comp f.1) ≤ L*A f.1+δ) :
    Variational.leastCost (fun f : {f : C(S,N) // ContMDiff IS IN 1 f ∧ NonNull f} => B f.1) ≤
      L*Variational.leastCost (fun f : {f : C(S,M) // ContMDiff IS IM 1 f ∧ NonNull f} => A f.1)+δ :=
/- SWARM_PROOF_BEGIN -/
by
  let T : {f : C(S, M) // ContMDiff IS IM 1 f ∧ NonNull f} →
      {f : C(S, N) // ContMDiff IS IN 1 f ∧ NonNull f} := fun f =>
    ⟨p.comp f.1,
      ⟨hp.comp f.property.1,
        (nonNull_comp_iff_of_left_homotopy_inverse p r hr f.1).mpr f.property.2⟩⟩
  have hN : Nonempty {f : C(S, N) // ContMDiff IS IN 1 f ∧ NonNull f} :=
    Nonempty.map T ‹Nonempty {f : C(S, M) // ContMDiff IS IM 1 f ∧ NonNull f}›
  exact @Variational.leastCost_transfer
    {f : C(S, M) // ContMDiff IS IM 1 f ∧ NonNull f}
    {f : C(S, N) // ContMDiff IS IN 1 f ∧ NonNull f}
    ‹Nonempty {f : C(S, M) // ContMDiff IS IM 1 f ∧ NonNull f}› hN
    (fun f => A f.1) (fun f => B f.1) hA hB T L δ hL fun f => by
      simpa [T] using hb f
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
