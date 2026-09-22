import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- A disconnected open piece would disconnect a connected ambient cover if its overlap is connected. -/
theorem open_piece_preconnected {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hinter : IsPreconnected (U ∩ V)) : IsPreconnected U :=
/- SWARM_PROOF_BEGIN -/
by
  intro a b ha hb hsub hna hnb
  by_contra hne
  have hab : U ∩ (a ∩ b) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  have hnot : ∀ {x : X}, x ∈ U → x ∈ a → x ∈ b → False := by
    intro x hxU hxa hxb
    have hx : x ∈ U ∩ (a ∩ b) := ⟨hxU, hxa, hxb⟩
    rw [hab] at hx
    exact hx
  have hcoverI : U ∩ V ⊆ (a ∩ U) ∪ (b ∩ U) := by
    intro x hx
    rcases hsub hx.1 with hxa | hxb
    · exact Or.inl ⟨hxa, hx.1⟩
    · exact Or.inr ⟨hxb, hx.1⟩
  have hdisjI : Disjoint (a ∩ U) (b ∩ U) := by
    refine Set.disjoint_left.2 ?_
    intro x hxa hxb
    exact hnot hxa.2 hxa.1 hxb.1
  rcases hinter.subset_or_subset (ha.inter hU) (hb.inter hU) hdisjI hcoverI with hleft | hright
  · have hcoverX : (univ : Set X) ⊆ (b ∩ U) ∪ ((a ∩ U) ∪ V) := by
      intro x hx
      rw [← hcover] at hx
      rcases hx with hxU | hxV
      · rcases hsub hxU with hxa | hxb
        · exact Or.inr (Or.inl ⟨hxa, hxU⟩)
        · exact Or.inl ⟨hxb, hxU⟩
      · exact Or.inr (Or.inr hxV)
    have hdisjX : Disjoint (b ∩ U) ((a ∩ U) ∪ V) := by
      refine Set.disjoint_left.2 ?_
      intro x hxb hx
      rcases hx with hxa | hxV
      · exact hnot hxb.2 hxa.1 hxb.1
      · have hxa := hleft ⟨hxb.2, hxV⟩
        exact hnot hxb.2 hxa.1 hxb.1
    have hnonempty₁ : (b ∩ U).Nonempty := by
      simpa [inter_comm] using hnb
    have hnonempty₂ : ((a ∩ U) ∪ V).Nonempty := by
      rcases hna with ⟨x, hxU, hxa⟩
      exact ⟨x, Or.inl ⟨hxa, hxU⟩⟩
    have hnonempty₁' : (univ ∩ (b ∩ U)).Nonempty := by simpa using hnonempty₁
    have hnonempty₂' : (univ ∩ ((a ∩ U) ∪ V)).Nonempty := by simpa using hnonempty₂
    rcases isPreconnected_univ (b ∩ U) ((a ∩ U) ∪ V)
        (hb.inter hU) ((ha.inter hU).union hV) hcoverX hnonempty₁' hnonempty₂' with
      ⟨x, -, hx⟩
    exact (Set.disjoint_left.1 hdisjX) hx.1 hx.2
  · have hcoverX : (univ : Set X) ⊆ (a ∩ U) ∪ ((b ∩ U) ∪ V) := by
      intro x hx
      rw [← hcover] at hx
      rcases hx with hxU | hxV
      · rcases hsub hxU with hxa | hxb
        · exact Or.inl ⟨hxa, hxU⟩
        · exact Or.inr (Or.inl ⟨hxb, hxU⟩)
      · exact Or.inr (Or.inr hxV)
    have hdisjX : Disjoint (a ∩ U) ((b ∩ U) ∪ V) := by
      refine Set.disjoint_left.2 ?_
      intro x hxa hx
      rcases hx with hxb | hxV
      · exact hnot hxa.2 hxa.1 hxb.1
      · have hxb := hright ⟨hxa.2, hxV⟩
        exact hnot hxa.2 hxa.1 hxb.1
    have hnonempty₁ : (a ∩ U).Nonempty := by
      simpa [inter_comm] using hna
    have hnonempty₂ : ((b ∩ U) ∪ V).Nonempty := by
      rcases hnb with ⟨x, hxU, hxb⟩
      exact ⟨x, Or.inl ⟨hxb, hxU⟩⟩
    have hnonempty₁' : (univ ∩ (a ∩ U)).Nonempty := by simpa using hnonempty₁
    have hnonempty₂' : (univ ∩ ((b ∩ U) ∪ V)).Nonempty := by simpa using hnonempty₂
    rcases isPreconnected_univ (a ∩ U) ((b ∩ U) ∪ V)
        ((ha.inter hU)) ((hb.inter hU).union hV) hcoverX hnonempty₁' hnonempty₂' with
      ⟨x, -, hx⟩
    exact (Set.disjoint_left.1 hdisjX) hx.1 hx.2
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
