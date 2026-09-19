import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import PoincareConjecture.Topology.FiberSaturation.TorusShortStrip
import Mathlib.Topology.Covering.Quotient

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** The actual infinite-cylinder quotient is a covering map; local injectivity alone is not the conclusion. -/
theorem mappingTorus_projection_isCoveringMap {X : Type*} [TopologicalSpace X]
    (phi : X ≃ₜ X) (L : ℝ) (hL : 0 < L) :
    IsCoveringMap (PoincareConjecture.Topology.FiberSaturation.MappingTorus.proj phi L) :=
/- SWARM_PROOF_BEGIN -/
open PoincareConjecture.Topology.FiberSaturation.MappingTorus in
by
  letI : AddAction ℤ (X × ℝ) :=
    { vadd := fun n p => deck phi L n p
      zero_vadd := deck_zero phi L
      add_vadd := fun m n p => deck_add phi L m n p }
  letI : ContinuousConstVAdd ℤ (X × ℝ) :=
    ⟨fun n => (deck phi L n).continuous⟩
  refine (show IsAddQuotientCoveringMap (proj phi L) ℤ from ?_).isCoveringMap
  refine
    { toIsQuotientMap := isQuotientMap_quotient_mk'
      continuous_const_vadd := fun n => (deck phi L n).continuous
      apply_eq_iff_mem_orbit := ?orbit
      disjoint := ?disjoint }
  · intro e₁ e₂
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
  · intro e
    let r : ℝ := L / 4
    have hr : 0 < r := div_pos hL (by norm_num)
    let U : Set (X × ℝ) := univ ×ˢ Ioo (e.2 - r) (e.2 + r)
    have hUo : IsOpen U := isOpen_univ.prod isOpen_Ioo
    have heU : e ∈ U := ⟨mem_univ _, sub_lt_self _ hr, lt_add_of_pos_right _ hr⟩
    refine ⟨U, hUo.mem_nhds heU, fun n hne => ?_⟩
    obtain ⟨p, ⟨q, hqU, rfl⟩, hpU⟩ := hne
    have hsnd : (n +ᵥ q).2 = q.2 + (n : ℝ) * L := by
      change (deck phi L n q).2 = _
      simp [deck]
    have hw : (e.2 + r) - (e.2 - r) < L := by
      have : (e.2 + r) - (e.2 - r) = L / 2 := by
        simp [r]
        ring
      linarith
    have hqI : q.2 ∈ Icc (e.2 - r) (e.2 + r) := ⟨hqU.2.1.le, hqU.2.2.le⟩
    have hpI : (n +ᵥ q).2 ∈ Icc (e.2 - r) (e.2 + r) := ⟨hpU.2.1.le, hpU.2.2.le⟩
    exact integer_shift_zero hL hw hqI (hsnd ▸ hpI) hsnd
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
