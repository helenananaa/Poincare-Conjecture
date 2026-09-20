import Mathlib
import LeeSmoothLib.Ch05.Sec05_28.Proposition_5_2

-- Declarations for this item will be appended below by the statement pipeline.

-- The induced image structure is supplied by the verified Proposition 5.2.

open scoped Manifold ContDiff Topology
open Manifold Set Function

noncomputable section

universe u𝕜 uE uH uM uE' uH' uN

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ N]

/-- The canonical parametrization of the slice `M × {p}` in the product manifold `M × N`. -/
def productSliceMap (p : N) : M → M × N :=
  fun x ↦ (x, p)

omit [TopologicalSpace M] [TopologicalSpace N] in
/-- The image of `productSliceMap p` is exactly the slice `M × {p}`. -/
-- Proof sketch: unwind the definitions of `productSliceMap`, `Set.range`, and the product of sets;
-- a point lies in the range exactly when its second coordinate is `p`.
theorem range_productSliceMap_eq_univ_prod_singleton (p : N) :
    Set.range (productSliceMap p : M → M × N) = (Set.univ : Set M) ×ˢ ({p} : Set N) := by
  ext q
  simp only [Set.mem_range, Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro h
    exact ⟨q.1, Prod.ext rfl h.symm⟩

private def sliceShift [J.Boundaryless] (c : E') : H' ≃ₜ H' :=
  (J.toHomeomorph.trans (Homeomorph.addRight (-c))).trans J.toHomeomorph.symm

private lemma sliceShift_apply [J.Boundaryless] (c : E') (h : H') :
    J (sliceShift (J := J) c h) = J h - c := by
  change J (J.symm (J h + -c)) = J h - c
  rw [J.right_inv (by rw [J.range_eq_univ]; trivial)]
  simp [sub_eq_add_neg]

private lemma sliceShift_symm_apply [J.Boundaryless] (c : E') (h : H') :
    J ((sliceShift (J := J) c).symm h) = J h + c := by
  have ht := sliceShift_apply (J := J) c ((sliceShift (J := J) c).symm h)
  rw [Homeomorph.apply_symm_apply] at ht
  exact sub_eq_iff_eq_add.mp ht.symm

private lemma sliceShift_mem [J.Boundaryless] (c : E') :
    (sliceShift (J := J) c).toOpenPartialHomeomorph ∈ contDiffGroupoid ∞ J := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · change ContDiffOn 𝕜 ∞ (J ∘ sliceShift (J := J) c ∘ J.symm) _
    have hfun : (J ∘ sliceShift (J := J) c ∘ J.symm) = fun x : E' ↦ x - c := by
      funext x
      simp only [Function.comp_apply, sliceShift_apply]
      rw [J.right_inv (by rw [J.range_eq_univ]; trivial)]
    rw [hfun]
    exact (contDiff_id.sub contDiff_const).contDiffOn
  · change ContDiffOn 𝕜 ∞ (J ∘ (sliceShift (J := J) c).symm ∘ J.symm) _
    have hfun : (J ∘ (sliceShift (J := J) c).symm ∘ J.symm) = fun x : E' ↦ x + c := by
      funext x
      simp only [Function.comp_apply, sliceShift_symm_apply]
      rw [J.right_inv (by rw [J.range_eq_univ]; trivial)]
    rw [hfun]
    exact (contDiff_id.add contDiff_const).contDiffOn

private lemma sliceChart_mem [J.Boundaryless] (p : N) (c : E') :
    (chartAt H' p).trans (sliceShift (J := J) c).toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas J ∞ N := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e he
  have hc := IsManifold.chart_mem_maximalAtlas (I := J) (n := ∞) p
  have he' := IsManifold.subset_maximalAtlas (I := J) (n := ∞) he
  have hleft := IsManifold.compatible_of_mem_maximalAtlas hc he'
  have hright := IsManifold.compatible_of_mem_maximalAtlas he' hc
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ∞ J).trans
      ((contDiffGroupoid ∞ J).symm (sliceShift_mem (J := J) c)) hleft
  · simpa [OpenPartialHomeomorph.trans_assoc] using
      (contDiffGroupoid ∞ J).trans hright (sliceShift_mem (J := J) c)

/-- The canonical product-slice parametrization is a smooth embedding.
The frozen factor has no boundary; this is the ordinary-manifold setting of Lee's proposition.
The moving factor is allowed to have boundary. -/
theorem productSliceMap_isSmoothEmbedding [J.Boundaryless] (p : N) :
    Manifold.IsSmoothEmbedding I (I.prod J) ∞ (productSliceMap p : M → M × N) := by
  refine ⟨?_, ?_⟩
  · apply IsImmersionOfComplement.isImmersion (F := E')
    intro x
    let c : E' := J (chartAt H' p p)
    let e : OpenPartialHomeomorph N H' :=
      (chartAt H' p).trans (sliceShift (J := J) c).toOpenPartialHomeomorph
    have he : e ∈ IsManifold.maximalAtlas J ∞ N := sliceChart_mem p c
    refine IsImmersionAtOfComplement.mk_of_continuousAt
      (I := I) (J := I.prod J) (f := productSliceMap p)
      (by change ContinuousAt (fun x : M ↦ (x, p)) x; fun_prop) (ContinuousLinearEquiv.refl 𝕜 (E × E'))
      (chartAt H x) ((chartAt H x).prod e)
      (mem_chart_source H x) ?_
      (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.mem_maximalAtlas_prod (IsManifold.chart_mem_maximalAtlas x) he) ?_
    · exact ⟨mem_chart_source H x, ⟨mem_chart_source H' p, mem_univ _⟩⟩
    · intro y hy
      have hy' := ((chartAt H x).extend I).right_inv hy
      change ((I.prod J) (((chartAt H x).prod e)
        (productSliceMap p (((chartAt H x).extend I).symm y)))) = (y, 0)
      apply Prod.ext
      · exact hy'
      · change J (sliceShift (J := J) c (chartAt H' p p)) = 0
        rw [sliceShift_apply]
        exact sub_self c
  · exact (show LeftInverse (Prod.fst : M × N → M) (productSliceMap p) from
      fun _ ↦ rfl).isEmbedding continuous_fst
        (by change Continuous (fun x : M ↦ (x, p)); fun_prop)

/-- Proposition 5.3: the slice inherits its smooth structure from `M` via its canonical
parametrization. The no-boundary hypothesis on the frozen factor is explicit. -/
theorem product_slice_has_induced_manifold_structure [J.Boundaryless] (p : N) :
    ∃ (_ : ChartedSpace H (Set.range (productSliceMap p : M → M × N)))
      (_ : IsManifold I ∞ (Set.range (productSliceMap p : M → M × N))),
        Manifold.IsSmoothEmbedding I (I.prod J) ∞
          (Subtype.val : Set.range (productSliceMap p : M → M × N) → M × N) ∧
        ∃ Φ : M ≃ₘ⟮I, I⟯ Set.range (productSliceMap p : M → M × N),
          ∀ x,
            ((Φ x : Set.range (productSliceMap p : M → M × N)) : M × N) =
              productSliceMap p x := by
  obtain ⟨cs, hcs⟩ := smooth_embedding_range_has_induced_manifold_structure
    (productSliceMap_isSmoothEmbedding (I := I) (J := J) (M := M) p)
  exact ⟨cs, hcs⟩

end
