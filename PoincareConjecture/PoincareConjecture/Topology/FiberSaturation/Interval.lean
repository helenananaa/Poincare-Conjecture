import PoincareConjecture.Topology.FiberSaturation.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- A nonempty bounded connected open real set is its endpoint interval. -/
theorem open_connected_eq_Ioo {A : Set ℝ} (hopen : IsOpen A)
    (hconn : IsConnected A) (hbelow : BddBelow A) (habove : BddAbove A) :
    A = Ioo (sInf A) (sSup A) := by
  apply Subset.antisymm ?_ (hconn.Ioo_csInf_csSup_subset hbelow habove)
  intro x hx
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hx)
  obtain ⟨v, hlv, hvx⟩ := exists_between hl
  obtain ⟨w, hxw, hwu⟩ := exists_between hu
  exact ⟨lt_of_le_of_lt (csInf_le hbelow (hsub ⟨hlv, hvx.trans hu⟩)) hvx,
    lt_of_lt_of_le hxw (le_csSup habove (hsub ⟨hl.trans hxw, hwu⟩))⟩

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

/-- Relative version: compact closure in an open real parameter domain
forces two distinct endpoints inside that domain. The frontier is relative
to `X × J`, not the ambient `X × ℝ`. -/
theorem exists_interval_of_compact_closure {J : Set ℝ} (hJ : IsOpen J)
    {U : Set (X × J)} (hU : IsOpen U) (hconn : IsConnected U)
    (hfront : FiberSaturated (frontier U)) (hcompact : IsCompact (closure U)) :
    ∃ a b : ℝ, a < b ∧ a ∈ J ∧ b ∈ J ∧
      U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo a b) ∧
      frontier U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' {a, b}) := by
  let B : Set ℝ := (Subtype.val : J → ℝ) '' (Prod.snd '' U)
  let K : Set ℝ := (fun p : X × J => (p.2 : ℝ)) '' closure U
  have hBopen : IsOpen B :=
    hJ.isOpenMap_subtype_val _ (isOpenMap_snd U hU)
  have hBconn : IsConnected B :=
    (hconn.image _ continuous_snd.continuousOn).image _
      continuous_subtype_val.continuousOn
  have hK : IsCompact K :=
    hcompact.image (continuous_subtype_val.comp continuous_snd)
  have hBK : B ⊆ K := by
    rintro t ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, subset_closure hp, rfl⟩
  have hclosure : closure B ⊆ K := closure_minimal hBK hK.isClosed
  have hb : BddBelow B := hK.bddBelow.mono hBK
  have ha : BddAbove B := hK.bddAbove.mono hBK
  have hI : B = Ioo (sInf B) (sSup B) := open_connected_eq_Ioo hBopen hBconn hb ha
  have hab : sInf B < sSup B := by
    obtain ⟨t, ht⟩ := hBconn.nonempty
    rw [hI] at ht
    exact ht.1.trans ht.2
  have hKJ : K ⊆ J := by
    rintro t ⟨p, _, rfl⟩
    exact p.2.property
  have hleft : sInf B ∈ J :=
    hKJ (hclosure (csInf_mem_closure hBconn.nonempty hb))
  have hright : sSup B ∈ J :=
    hKJ (hclosure (csSup_mem_closure hBconn.nonempty ha))
  have hbase : Prod.snd '' U = (Subtype.val : J → ℝ) ⁻¹' B := by
    simp only [B, preimage_image_eq _ Subtype.val_injective]
  have hprod : U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo (sInf B) (sSup B)) := by
    calc
      U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' B) := by
        rw [eq_univ_prod_image_of_frontier hU hfront, hbase]
      _ = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo (sInf B) (sSup B)) :=
        congrArg (fun A : Set ℝ => (univ : Set X) ×ˢ ((Subtype.val : J → ℝ) ⁻¹' A)) hI
  refine ⟨sInf B, sSup B, hab, hleft, hright, hprod, ?_⟩
  rw [hprod, frontier_univ_prod_eq,
    ← hJ.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val, frontier_Ioo hab]


/-- The unbounded/empty cases are retained: the real base is open and order-connected. -/
theorem exists_open_ordConnected_base {J : Set ℝ} (hJ : IsOpen J)
    {U : Set (X × J)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hfront : FiberSaturated (frontier U)) :
    ∃ A : Set ℝ, IsOpen A ∧ OrdConnected A ∧ A ⊆ J ∧
      U = univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' A) := by
  let A : Set ℝ := (Subtype.val : J → ℝ) '' (Prod.snd '' U)
  have ho : IsOpen A := hJ.isOpenMap_subtype_val _ (isOpenMap_snd U hU)
  have hc : IsPreconnected A :=
    (hconn.image _ continuous_snd.continuousOn).image _
      continuous_subtype_val.continuousOn
  refine ⟨A, ho, hc.ordConnected, ?_, ?_⟩
  · rintro t ⟨y, _, rfl⟩
    exact y.property
  · simpa only [A, preimage_image_eq _ Subtype.val_injective] using
      eq_univ_prod_image_of_frontier hU hfront

end PoincareConjecture.Topology.FiberSaturation
