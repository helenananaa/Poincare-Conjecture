import PoincareConjecture.ParallelMath.Transfer.HomotopyLeftInverse
import PoincareConjecture.ParallelMath.Variational.AdmissibleTransfer
import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- A left homotopy inverse supplies the actual map of nontrivial admissible maps needed for least-cost transfer. -/
theorem nonNull_leastCost_transport
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Nonempty (NonNullMap X Y)]
    (p : C(Y,Z)) (r : C(Z,Y)) (hr : (r.comp p).Homotopic (ContinuousMap.id Y))
    (A : C(X,Y) → ℝ) (B : C(X,Z) → ℝ)
    (hA : ∀ f : NonNullMap X Y, 0 ≤ A f.1)
    (hB : ∀ f : NonNullMap X Z, 0 ≤ B f.1)
    (L δ : ℝ) (hL : 0 ≤ L)
    (hb : ∀ f : NonNullMap X Y, B (p.comp f.1) ≤ L*A f.1+δ) :
    Variational.leastCost (fun f : NonNullMap X Z => B f.1) ≤
      L*Variational.leastCost (fun f : NonNullMap X Y => A f.1)+δ :=
/- SWARM_PROOF_BEGIN -/
by
  let T : NonNullMap X Y → NonNullMap X Z := fun f =>
    ⟨p.comp f.1, (nonNull_comp_iff_of_left_homotopy_inverse p r hr f.1).mpr f.2⟩
  have hZ : Nonempty (NonNullMap X Z) := Nonempty.map T ‹Nonempty (NonNullMap X Y)›
  exact @Variational.leastCost_transfer (NonNullMap X Y) (NonNullMap X Z)
    ‹Nonempty (NonNullMap X Y)› hZ
    (fun f => A f.1) (fun f => B f.1) hA hB T L δ hL fun f => by
      simpa [T] using hb f
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
