import PoincareConjecture.Topology.FiberSaturation.SmoothPresentedCylinder

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set Manifold
open scoped Manifold ContDiff

variable {E F H G X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace X] [ChartedSpace H X] [PreconnectedSpace X]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [IsManifold I ∞ X]

/-- Smooth product-neck classification in the original smooth structure of
the domain closure. The target uses the standard interval boundary structure. -/
theorem product_region_diffeomorph {U : Set (X × ℝ)}
    [ChartedSpace G (closure U)] [IsManifold J ∞ (closure U)] (hU : IsOpen U) (hc : IsConnected U)
    (hfront : FiberSaturated (frontier U)) (hk : IsCompact (closure U))
    (hf : IsSmoothEmbedding J (I.prod 𝓘(ℝ, ℝ)) ∞ (Subtype.val : closure U → X × ℝ)) :
    Nonempty (↥(closure U) ≃ₘ⟮J, I.prod (𝓡∂ 1)⟯ (X × Icc (0 : ℝ) 1)) := by
  let A : Set ℝ := Prod.snd '' U
  have hA : IsConnected A := hc.image _ continuous_snd.continuousOn
  have hbound := hk.image continuous_snd
  have hAsub : A ⊆ Prod.snd '' closure U := image_mono subset_closure
  have hshape : A = Ioo (sInf A) (sSup A) := open_connected_eq_Ioo
    (isOpenMap_snd U hU) hA (hbound.bddBelow.mono hAsub) (hbound.bddAbove.mono hAsub)
  have hab : sInf A < sSup A := by
    obtain ⟨t, ht⟩ := hA.nonempty
    rw [hshape] at ht
    exact ht.1.trans ht.2
  letI : Fact (sInf A < sSup A) := ⟨hab⟩
  have hUshape : U = univ ×ˢ Ioo (sInf A) (sSup A) := by
    exact (eq_univ_prod_image_of_frontier hU hfront).trans
      (congrArg (fun B : Set ℝ => (univ : Set X) ×ˢ B) hshape)
  have hcl : closure U = univ ×ˢ Icc (sInf A) (sSup A) := by
    rw [hUshape, closure_prod_eq, closure_univ, closure_Ioo hab.ne]
  have hrange : range (Subtype.val : closure U → X × ℝ) =
      range (fun p : X × Icc (sInf A) (sSup A) => (p.1, (p.2 : ℝ))) := by
    rw [Subtype.range_val, hcl]
    ext p
    exact ⟨fun hp => ⟨(p.1, ⟨p.2, hp.2⟩), rfl⟩,
      by rintro ⟨q, rfl⟩; exact ⟨mem_univ _, q.2.2⟩⟩
  let d := diffeomorphOfEqualEmbeddingRange hf
    (cylinder_inclusion_smoothEmbedding I (sInf A) (sSup A)) hrange
  exact ⟨d.trans (cylinderDiffeomorphUnit I (sInf A) (sSup A))⟩

end PoincareConjecture.Topology.FiberSaturation
