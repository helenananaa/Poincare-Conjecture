import PoincareConjecture.ProofContract.Proofs.CoordinateBoundary
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Removing an open coordinate three-ball does not disconnect a closed connected manifold. -/
theorem coordinate_complement_connected {M : ClosedThreeManifold.{u}}
    (b : CoordinateBall M) : ConnectedSpace b.Complement :=
/- SWARM_PROOF_BEGIN -/
by
  have hsphere : IsConnected (Metric.sphere (0 : Euclidean3) 1) := by
    apply isConnected_sphere ?_ _ (by norm_num)
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hsource : Metric.sphere (0 : Euclidean3) 1 ⊆ b.parametrization.source := by
    intro x hx
    apply b.contains_two
    have hxnorm : ‖x‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hx
    simp [Metric.mem_closedBall, hxnorm]
  have hfrontier : IsConnected (frontier b.removed) := by
    rw [(coordinate_closure_frontier b).2]
    exact hsphere.image b.parametrization
      (b.parametrization.continuousOn.mono hsource)
  have hopen : IsOpen b.removed :=
    (coordinate_removed_open_complement_compact b).1
  have hclosed : IsClosed b.removedᶜ := isClosed_compl_iff.mpr hopen
  have hfrontier_compl : frontier b.removed ⊆ b.removedᶜ := by
    intro x hx
    rw [hopen.frontier_eq] at hx
    exact hx.2
  have hremoved_nonempty : b.removed.Nonempty := by
    refine ⟨b.parametrization 0, ?_⟩
    exact ⟨0, by simp, rfl⟩
  have hside : ∀ {u v : Set M}, IsOpen u → IsOpen v →
      b.removedᶜ ⊆ u ∪ v → b.removedᶜ ∩ (u ∩ v) = ∅ →
      frontier b.removed ⊆ u → b.removedᶜ ⊆ u := by
    intro u v hu hv hcover hdisj hboundary
    let d : Set M := b.removedᶜ \ u
    have hdclosed : IsClosed d := by
      dsimp [d]
      exact hclosed.inter hu.isClosed_compl
    have hdeq : d = interior b.removedᶜ ∩ v := by
      ext x
      constructor
      · intro hx
        have hxfrontier : x ∉ frontier b.removed := by
          intro hxf
          exact hx.2 (hboundary hxf)
        have hxinterior : x ∈ interior b.removedᶜ := by
          apply (mem_interior_iff_notMem_frontier hx.1).2
          simpa only [frontier_compl] using hxfrontier
        have hxv : x ∈ v := by
          rcases hcover hx.1 with hxu | hxv
          · exact (hx.2 hxu).elim
          · exact hxv
        exact ⟨hxinterior, hxv⟩
      · rintro ⟨hxinterior, hxv⟩
        refine ⟨interior_subset hxinterior, ?_⟩
        intro hxu
        have hxdisj : x ∈ b.removedᶜ ∩ (u ∩ v) :=
          ⟨interior_subset hxinterior, hxu, hxv⟩
        rw [hdisj] at hxdisj
        exact hxdisj
    have hdopen : IsOpen d := by
      rw [hdeq]
      exact isOpen_interior.inter hv
    have hdclopen : IsClopen d := ⟨hdclosed, hdopen⟩
    have hdempty : d = ∅ := by
      rcases isClopen_iff.mp hdclopen with hd | hd
      · exact hd
      · exfalso
        obtain ⟨x, hx⟩ := hremoved_nonempty
        have hxd : x ∈ d := by
          rw [hd]
          exact mem_univ x
        exact hxd.1 hx
    intro x hx
    by_contra hxu
    have hxd : x ∈ d := ⟨hx, hxu⟩
    rw [hdempty] at hxd
    exact hxd
  have hpreconnected : IsPreconnected b.removedᶜ := by
    apply isPreconnected_iff_subset_of_disjoint.mpr
    intro u v hu hv hcover hdisj
    have hfrontier_cover : frontier b.removed ⊆ u ∪ v :=
      hfrontier_compl.trans hcover
    have hfrontier_disjoint : frontier b.removed ∩ (u ∩ v) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxdisj : x ∈ b.removedᶜ ∩ (u ∩ v) :=
        ⟨hfrontier_compl hx.1, hx.2⟩
      rw [hdisj] at hxdisj
      exact hxdisj
    rcases (isPreconnected_iff_subset_of_disjoint.mp hfrontier.isPreconnected
      u v hu hv hfrontier_cover hfrontier_disjoint) with hU | hV
    · exact Or.inl (hside hu hv hcover hdisj hU)
    · exact Or.inr (hside hv hu (by simpa [union_comm] using hcover)
        (by simpa [inter_comm] using hdisj) hV)
  exact Subtype.connectedSpace
    ⟨hfrontier.nonempty.mono hfrontier_compl, hpreconnected⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
