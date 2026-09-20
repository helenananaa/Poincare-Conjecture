import PoincareConjecture.ParallelMath.Transport.TorusUniversal
import PoincareConjecture.Topology.FiberSaturation.MappingTorus
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath.Transport
open PoincareConjecture.Topology.FiberSaturation.MappingTorus
open Set

/-- For a simply connected fiber, the mapping torus has fundamental group
isomorphic to `ℤ`. Does not classify sphere bundles and does not require
`Sphere2`. -/
theorem mappingTorus_fundamentalGroup_equiv_int
    {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X] [PathConnectedSpace X]
    (phi : X ≃ₜ X) (L : ℝ) (hL : 0 < L)
    (p : Space phi L) :
    Nonempty (FundamentalGroup (Space phi L) p ≃* Multiplicative ℤ) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨_, hsc, _hfiber⟩ := mappingTorus_universal_cover_data phi L hL
  letI : AddAction ℤ (X × ℝ) :=
    { vadd := fun n q => deck phi L n q
      zero_vadd := deck_zero phi L
      add_vadd := fun m n q => deck_add phi L m n q }
  letI : ContinuousConstVAdd ℤ (X × ℝ) :=
    ⟨fun n => (deck phi L n).continuous⟩
  have cov : IsAddQuotientCoveringMap (proj phi L) ℤ :=
    { toIsQuotientMap := isQuotientMap_quotient_mk'
      continuous_const_vadd := fun n => (deck phi L n).continuous
      apply_eq_iff_mem_orbit := by
        intro e₁ e₂
        rw [proj_eq_iff, AddAction.mem_orbit_iff]
        constructor
        · rintro ⟨n, hn⟩
          refine ⟨-n, ?_⟩
          change deck phi L (-n) e₂ = e₁
          rw [← hn, ← deck_add, neg_add_cancel, deck_zero]
        · rintro ⟨n, hn⟩
          refine ⟨-n, ?_⟩
          have hn' : deck phi L n e₂ = e₁ := hn
          rw [← hn', ← deck_add, neg_add_cancel, deck_zero]
      disjoint := by
        intro e
        let r : ℝ := L / 4
        have hr : 0 < r := div_pos hL (by norm_num)
        let U : Set (X × ℝ) := univ ×ˢ Ioo (e.2 - r) (e.2 + r)
        have hUo : IsOpen U := isOpen_univ.prod isOpen_Ioo
        have heU : e ∈ U := ⟨mem_univ _, sub_lt_self _ hr, lt_add_of_pos_right _ hr⟩
        refine ⟨U, hUo.mem_nhds heU, fun n hne => ?_⟩
        obtain ⟨q', ⟨q, hqU, rfl⟩, hq'U⟩ := hne
        have hsnd : (n +ᵥ q).2 = q.2 + (n : ℝ) * L := by
          change (deck phi L n q).2 = _
          simp [deck]
        have hw : (e.2 + r) - (e.2 - r) < L := by
          have : (e.2 + r) - (e.2 - r) = L / 2 := by
            simp [r]
            ring
          linarith
        have hqI : q.2 ∈ Icc (e.2 - r) (e.2 + r) := ⟨hqU.2.1.le, hqU.2.2.le⟩
        have hq'I : (n +ᵥ q).2 ∈ Icc (e.2 - r) (e.2 + r) := ⟨hq'U.2.1.le, hq'U.2.2.le⟩
        exact integer_shift_zero hL hw hqI (hsnd ▸ hq'I) hsnd }
  letI : SimplyConnectedSpace (X × ℝ) := hsc
  obtain ⟨t, ht⟩ := cov.surjective p
  exact ⟨(cov.fundamentalGroupEquiv ⟨t, ht⟩).trans MulOpposite.opMulEquiv.symm⟩
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath.Transport
