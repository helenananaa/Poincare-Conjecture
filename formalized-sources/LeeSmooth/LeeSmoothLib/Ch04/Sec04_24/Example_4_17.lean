import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Lemmas
-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the statement
-- shapes were fixed from mathlib's `Manifold.IsSmoothEmbedding.of_opens` and the local torus
-- embedding theorem in `Problem_4_12`.

noncomputable section

open Manifold Function Set Topology
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

universe uE uH uM

/- Recall for Example 4.17: the canonical mathlib theorem
`Manifold.IsSmoothEmbedding.of_opens` is exactly the statement that the inclusion of an open
submanifold `U ↪ M` is a smooth embedding. -/
#check Manifold.IsSmoothEmbedding.of_opens

section FiniteProductInclusions

variable {k : ℕ}
variable {E : Fin k → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
variable {H : Fin k → Type uH} [∀ i, TopologicalSpace (H i)]
variable {I : ∀ i, ModelWithCorners ℝ (E i) (H i)}
variable {M : Fin k → Type uM} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
variable [∀ i, IsManifold (I i) ∞ (M i)]
variable [IsManifold (ModelWithCorners.pi I) ∞ ((i : Fin k) → M i)]

/-- The inclusion of the `j`-th factor into a finite product of manifolds, obtained by freezing the
other coordinates at the chosen points `p i`. -/
def finite_product_inclusion (p : (i : Fin k) → M i) (j : Fin k) : M j → (i : Fin k) → M i :=
  fun q ↦ Function.update p j q

/-- Splitting a finite product of model spaces off the `j`-th factor. -/
def piSplitAtCLEquiv (j : Fin k) :
    ((i : Fin k) → E i) ≃L[ℝ] E j × (∀ i : { i : Fin k // i ≠ j }, E i) where
  toFun := Equiv.piSplitAt j E
  invFun := (Equiv.piSplitAt j E).symm
  left_inv := (Equiv.piSplitAt j E).left_inv
  right_inv := (Equiv.piSplitAt j E).right_inv
  map_add' := by
    intro x y
    ext <;> simp [Equiv.piSplitAt]
  map_smul' := by
    intro r x
    ext <;> simp [Equiv.piSplitAt]
  continuous_toFun := (Homeomorph.piSplitAt (Y := E) j).continuous
  continuous_invFun := (Homeomorph.piSplitAt (Y := E) j).continuous_invFun

lemma finite_product_inclusion_leftInverse (p : (i : Fin k) → M i) (j : Fin k) :
    LeftInverse (fun x : (i : Fin k) → M i ↦ x j) (finite_product_inclusion p j) := by
  intro q
  simp [finite_product_inclusion]

lemma finite_product_inclusion_continuous (p : (i : Fin k) → M i) (j : Fin k) :
    Continuous (finite_product_inclusion p j) :=
  continuous_pi fun i ↦ by
    by_cases h : i = j
    · rw [h]
      simp only [finite_product_inclusion, update_self]
      exact continuous_id
    · simp only [finite_product_inclusion, update_of_ne h]
      exact continuous_const

lemma finite_product_inclusion_isEmbedding (p : (i : Fin k) → M i) (j : Fin k) :
    IsEmbedding (finite_product_inclusion p j) :=
  (finite_product_inclusion_leftInverse p j).isEmbedding
    (continuous_apply j) (finite_product_inclusion_continuous p j)

/-- Finite products of boundaryless models are boundaryless. -/
instance pi_boundaryless [∀ i, (I i).Boundaryless] :
    (ModelWithCorners.pi I).Boundaryless where
  range_eq_univ := by
    ext x
    refine ⟨fun _ ↦ mem_univ _, fun _ ↦ ?_⟩
    refine mem_range.mpr ⟨fun i ↦ (I i).symm (x i), ?_⟩
    ext i
    change (I i) ((I i).symm (x i)) = x i
    exact (I i).right_inv (by rw [(I i).range_eq_univ]; exact mem_univ _)

/-- Extended-chart image of the frozen coordinates, with the moving slot set to `0`. -/
def frozenOffset (p : (i : Fin k) → M i) (j : Fin k) : (i : Fin k) → E i :=
  fun i ↦ if i = j then 0 else (I i) (chartAt (H i) (p i) (p i))

/-- Translation of the product model space which recentres frozen chart coordinates at the origin.
This is a global homeomorphism precisely when each factor model is boundaryless. -/
def frozenTranslationHomeomorph [∀ i, (I i).Boundaryless] (c : (i : Fin k) → E i) :
    ModelPi H ≃ₜ ModelPi H :=
  (((ModelWithCorners.pi I).toHomeomorph.trans (Homeomorph.addRight (-c))).trans
    (ModelWithCorners.pi I).toHomeomorph.symm)

lemma frozenTranslationHomeomorph_apply [∀ i, (I i).Boundaryless]
    (c : (i : Fin k) → E i) (h : ModelPi H) :
    frozenTranslationHomeomorph (I := I) c h =
      (ModelWithCorners.pi I).symm ((ModelWithCorners.pi I) h + (-c)) :=
  rfl

lemma pi_comp_frozenTranslationHomeomorph [∀ i, (I i).Boundaryless]
    (c : (i : Fin k) → E i) (h : ModelPi H) :
    (ModelWithCorners.pi I) (frozenTranslationHomeomorph (I := I) c h) =
      (ModelWithCorners.pi I) h - c := by
  rw [frozenTranslationHomeomorph_apply]
  have hmem : (ModelWithCorners.pi I) h + (-c) ∈ range (ModelWithCorners.pi I) := by
    rw [(ModelWithCorners.pi I).range_eq_univ]
    exact mem_univ _
  rw [ModelWithCorners.right_inv _ hmem]
  abel

lemma frozenTranslationHomeomorph_symm_apply [∀ i, (I i).Boundaryless]
    (c : (i : Fin k) → E i) (h : ModelPi H) :
    (frozenTranslationHomeomorph (I := I) c).symm h =
      (ModelWithCorners.pi I).symm ((ModelWithCorners.pi I) h + c) := by
  apply (ModelWithCorners.pi I).injective
  have hmem : (ModelWithCorners.pi I) h + c ∈ range (ModelWithCorners.pi I) := by
    rw [(ModelWithCorners.pi I).range_eq_univ]
    exact mem_univ _
  rw [ModelWithCorners.right_inv _ hmem]
  have hχ := pi_comp_frozenTranslationHomeomorph (I := I) c
    ((frozenTranslationHomeomorph (I := I) c).symm h)
  rw [Homeomorph.apply_symm_apply] at hχ
  exact eq_add_of_sub_eq hχ.symm

/-- Postcomposing a maximal-atlas chart with a smooth self-chart change of the model space stays in
the same maximal atlas. -/
lemma trans_mem_maximalAtlas_of_mem_groupoid
    {N : Type uM} [TopologicalSpace N] [ChartedSpace (ModelPi H) N]
    [IsManifold (ModelWithCorners.pi I) ∞ N]
    {e : OpenPartialHomeomorph N (ModelPi H)}
    (he : e ∈ IsManifold.maximalAtlas (ModelWithCorners.pi I) ∞ N)
    {chi : OpenPartialHomeomorph (ModelPi H) (ModelPi H)}
    (hchi : chi ∈ contDiffGroupoid ∞ (ModelWithCorners.pi I)) :
    e.trans chi ∈ IsManifold.maximalAtlas (ModelWithCorners.pi I) ∞ N := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  have he'max : e' ∈ IsManifold.maximalAtlas (ModelWithCorners.pi I) ∞ N :=
    IsManifold.subset_maximalAtlas he'
  have hleft : e.symm.trans e' ∈ contDiffGroupoid ∞ (ModelWithCorners.pi I) :=
    IsManifold.compatible_of_mem_maximalAtlas he he'max
  have hright : e'.symm.trans e ∈ contDiffGroupoid ∞ (ModelWithCorners.pi I) :=
    IsManifold.compatible_of_mem_maximalAtlas he'max he
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ∞ (ModelWithCorners.pi I)).trans
      ((contDiffGroupoid ∞ (ModelWithCorners.pi I)).symm hchi) hleft
  · have hright' :
        (e'.symm.trans e).trans chi ∈ contDiffGroupoid ∞ (ModelWithCorners.pi I) :=
      (contDiffGroupoid ∞ (ModelWithCorners.pi I)).trans hright hchi
    simpa [OpenPartialHomeomorph.trans_assoc] using hright'

lemma frozenTranslationHomeomorph_mem_contDiffGroupoid [∀ i, (I i).Boundaryless]
    (c : (i : Fin k) → E i) :
    (frozenTranslationHomeomorph (I := I) c).toOpenPartialHomeomorph ∈
      contDiffGroupoid ∞ (ModelWithCorners.pi I) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · change ContDiffOn ℝ ∞
        ((ModelWithCorners.pi I) ∘
          (frozenTranslationHomeomorph (I := I) c).toOpenPartialHomeomorph ∘
            (ModelWithCorners.pi I).symm)
        ((ModelWithCorners.pi I).symm ⁻¹'
            (frozenTranslationHomeomorph (I := I) c).toOpenPartialHomeomorph.source ∩
          range (ModelWithCorners.pi I))
    have hfun :
        ((ModelWithCorners.pi I) ∘
            (frozenTranslationHomeomorph (I := I) c).toOpenPartialHomeomorph ∘
              (ModelWithCorners.pi I).symm) =
          fun x : (i : Fin k) → E i ↦ x - c := by
      funext x
      change (ModelWithCorners.pi I)
          (frozenTranslationHomeomorph (I := I) c ((ModelWithCorners.pi I).symm x)) = x - c
      rw [pi_comp_frozenTranslationHomeomorph]
      have hx : x ∈ range (ModelWithCorners.pi I) := by
        rw [(ModelWithCorners.pi I).range_eq_univ]
        exact mem_univ _
      rw [ModelWithCorners.right_inv _ hx]
    have hdom :
        (ModelWithCorners.pi I).symm ⁻¹'
            (frozenTranslationHomeomorph (I := I) c).toOpenPartialHomeomorph.source ∩
          range (ModelWithCorners.pi I) = univ := by
      simp [Homeomorph.toOpenPartialHomeomorph_source, (ModelWithCorners.pi I).range_eq_univ]
    rw [hfun, hdom]
    exact (contDiff_id.sub (contDiff_const (c := c))).contDiffOn
  · change ContDiffOn ℝ ∞
        ((ModelWithCorners.pi I) ∘
          (frozenTranslationHomeomorph (I := I) c).toOpenPartialHomeomorph.symm ∘
            (ModelWithCorners.pi I).symm)
        ((ModelWithCorners.pi I).symm ⁻¹'
            (frozenTranslationHomeomorph (I := I) c).toOpenPartialHomeomorph.target ∩
          range (ModelWithCorners.pi I))
    have hfun :
        ((ModelWithCorners.pi I) ∘
            (frozenTranslationHomeomorph (I := I) c).toOpenPartialHomeomorph.symm ∘
              (ModelWithCorners.pi I).symm) =
          fun x : (i : Fin k) → E i ↦ x + c := by
      funext x
      change (ModelWithCorners.pi I)
          ((frozenTranslationHomeomorph (I := I) c).symm ((ModelWithCorners.pi I).symm x)) =
        x + c
      rw [frozenTranslationHomeomorph_symm_apply]
      have hx : x ∈ range (ModelWithCorners.pi I) := by
        rw [(ModelWithCorners.pi I).range_eq_univ]
        exact mem_univ _
      have hmem : (ModelWithCorners.pi I) ((ModelWithCorners.pi I).symm x) + c ∈
          range (ModelWithCorners.pi I) := by
        rw [(ModelWithCorners.pi I).range_eq_univ]
        exact mem_univ _
      rw [ModelWithCorners.right_inv _ hmem, ModelWithCorners.right_inv _ hx]
    have hdom' :
        (ModelWithCorners.pi I).symm ⁻¹'
            (frozenTranslationHomeomorph (I := I) c).toOpenPartialHomeomorph.target ∩
          range (ModelWithCorners.pi I) = univ := by
      simp [Homeomorph.toOpenPartialHomeomorph_target, (ModelWithCorners.pi I).range_eq_univ]
    rw [hfun, hdom']
    exact (contDiff_id.add (contDiff_const (c := c))).contDiffOn

lemma piSplitAtCLEquiv_symm_pair (j : Fin k) (y : E j) :
    (piSplitAtCLEquiv (E := E) j).symm (y, 0) = Function.update (0 : (i : Fin k) → E i) j y := by
  ext i
  change (Equiv.piSplitAt j E).symm (y, 0) i = Function.update (0 : (i : Fin k) → E i) j y i
  rw [Equiv.piSplitAt_symm_apply]
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

/-- Example 4.17 (1): fixing points in all but one factor, the inclusion of the remaining factor
into the finite product is a smooth embedding. -/
theorem finite_product_inclusion_isSmoothEmbedding
    [∀ i, (I i).Boundaryless]
    (p : (i : Fin k) → M i) (j : Fin k) :
    IsSmoothEmbedding (I j) (ModelWithCorners.pi I) ∞ (finite_product_inclusion p j) := by
  refine ⟨?immersion, finite_product_inclusion_isEmbedding p j⟩
  refine IsImmersionOfComplement.isImmersion
    (F := (i : { i : Fin k // i ≠ j }) → E i) ?_
  intro q
  let x0 : (i : Fin k) → M i := finite_product_inclusion p j q
  let c : (i : Fin k) → E i := frozenOffset (I := I) p j
  let chi : ModelPi H ≃ₜ ModelPi H := frozenTranslationHomeomorph (I := I) c
  let codChart : OpenPartialHomeomorph ((i : Fin k) → M i) (ModelPi H) :=
    (chartAt (ModelPi H) x0).transHomeomorph chi
  have hcod_eq : codChart = (chartAt (ModelPi H) x0).trans chi.toOpenPartialHomeomorph :=
    OpenPartialHomeomorph.transHomeomorph_eq_trans _ _
  have hcodAtlas : codChart ∈ IsManifold.maximalAtlas (ModelWithCorners.pi I) ∞
      ((i : Fin k) → M i) := by
    rw [hcod_eq]
    exact trans_mem_maximalAtlas_of_mem_groupoid
      (IsManifold.chart_mem_maximalAtlas x0)
      (frozenTranslationHomeomorph_mem_contDiffGroupoid (I := I) c)
  have hx0 : x0 ∈ codChart.source := by
    change x0 ∈ (chartAt (ModelPi H) x0).source
    exact mem_chart_source (ModelPi H) x0
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (finite_product_inclusion_continuous p j).continuousAt
    (piSplitAtCLEquiv (E := E) j).symm
    (chartAt (H j) q)
    codChart
    (mem_chart_source (H j) q)
    hx0
    (IsManifold.chart_mem_maximalAtlas q)
    hcodAtlas
  intro y hy
  have hy_inv :
      (I j) ((chartAt (H j) q)
        ((((chartAt (H j) q).extend (I j)).symm) y)) = y := by
    have := ((chartAt (H j) q).extend (I j)).right_inv hy
    simpa [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm] using this
  have hleft :
      (codChart.extend (ModelWithCorners.pi I)
        (finite_product_inclusion p j
          ((((chartAt (H j) q).extend (I j)).symm) y))) =
        Function.update (0 : (i : Fin k) → E i) j y := by
    have htrans :
        codChart.extend (ModelWithCorners.pi I)
            (finite_product_inclusion p j
              ((((chartAt (H j) q).extend (I j)).symm) y)) =
          (ModelWithCorners.pi I)
            (chi (chartAt (ModelPi H) x0
              (finite_product_inclusion p j
                ((((chartAt (H j) q).extend (I j)).symm) y)))) := by
      simp [codChart]
    rw [htrans, pi_comp_frozenTranslationHomeomorph]
    ext i
    rw [Pi.sub_apply]
    have hprod :
        ((ModelWithCorners.pi I)
            (chartAt (ModelPi H) x0
              (finite_product_inclusion p j
                ((((chartAt (H j) q).extend (I j)).symm) y)))) i =
          (I i) (chartAt (H i) (x0 i)
            (finite_product_inclusion p j
              ((((chartAt (H j) q).extend (I j)).symm) y) i)) :=
      rfl
    rw [hprod]
    by_cases hi : i = j
    · subst hi
      have hc : c i = 0 := by simp [c, frozenOffset]
      rw [hc, sub_zero]
      simp only [finite_product_inclusion, update_self, x0]
      exact hy_inv
    · have hx0i : x0 i = p i := update_of_ne hi q p
      have hfr :
          finite_product_inclusion p j
              ((((chartAt (H j) q).extend (I j)).symm) y) i = p i :=
        update_of_ne hi _ p
      have hc : c i = (I i) (chartAt (H i) (p i) (p i)) := by
        simp [c, frozenOffset, hi]
      rw [hx0i, hfr, hc, sub_self, update_of_ne hi, Pi.zero_apply]
  change
    (codChart.extend (ModelWithCorners.pi I)
      (finite_product_inclusion p j
        ((((chartAt (H j) q).extend (I j)).symm) y))) =
      (piSplitAtCLEquiv (E := E) j).symm (y, 0)
  rw [hleft, piSplitAtCLEquiv_symm_pair]

end FiniteProductInclusions

/-- The standard inclusion `ℝ^n ↪ ℝ^(n+k)` with trailing zero coordinates. -/
def euclidean_zero_tail_inclusion (n k : ℕ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + k)) :=
  fun x ↦ WithLp.toLp 2 (Fin.append x (fun _ : Fin k ↦ (0 : ℝ)))

lemma euclidean_zero_tail_inclusion_eq_finAddEquivProd (n k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclidean_zero_tail_inclusion n k x =
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).symm (x, 0) := by
  rw [WithLp.ext_iff]
  funext i
  have hleft :
      (euclidean_zero_tail_inclusion n k x).ofLp i =
        Fin.append (WithLp.ofLp x) (fun _ : Fin k ↦ (0 : ℝ)) i :=
    rfl
  rw [hleft]
  have hreindex :
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).symm (x, 0)).ofLp i =
        ((EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := Fin n) (κ := Fin k)).symm (x, 0)).ofLp
          (finSumFinEquiv.symm i) := by
    simp [EuclideanSpace.finAddEquivProd, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft']
  rw [hreindex]
  refine Fin.addCases (fun i₀ ↦ ?_) (fun i₀ ↦ ?_) i
  · rw [finSumFinEquiv_symm_apply_castAdd, Fin.append_left]
    rfl
  · rw [finSumFinEquiv_symm_apply_natAdd, Fin.append_right]
    rfl

lemma euclidean_zero_tail_inclusion_eq_comp (n k : ℕ) :
    euclidean_zero_tail_inclusion n k =
      ⇑(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).symm ∘
        fun x : EuclideanSpace ℝ (Fin n) ↦ (x, (0 : EuclideanSpace ℝ (Fin k))) := by
  funext x
  exact euclidean_zero_tail_inclusion_eq_finAddEquivProd n k x

lemma euclidean_zero_tail_inclusion_isEmbedding (n k : ℕ) :
    IsEmbedding (euclidean_zero_tail_inclusion n k) := by
  rw [euclidean_zero_tail_inclusion_eq_comp]
  exact
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).toHomeomorph.symm.isEmbedding.comp
      (isEmbedding_prodMkLeft (0 : EuclideanSpace ℝ (Fin k)))

lemma euclidean_zero_tail_inclusion_continuous (n k : ℕ) :
    Continuous (euclidean_zero_tail_inclusion n k) :=
  (euclidean_zero_tail_inclusion_isEmbedding n k).continuous

/-- Example 4.17 (2): the map `ℝ^n ↪ ℝ^(n+k)` sending `(x¹, …, xⁿ)` to
`(x¹, …, xⁿ, 0, …, 0)` is a smooth embedding. -/
theorem euclidean_zero_tail_inclusion_isSmoothEmbedding (n k : ℕ) :
    IsSmoothEmbedding (𝓡 n) (𝓡 (n + k)) ∞ (euclidean_zero_tail_inclusion n k) := by
  refine ⟨?immersion, euclidean_zero_tail_inclusion_isEmbedding n k⟩
  refine IsImmersionOfComplement.isImmersion (F := EuclideanSpace ℝ (Fin k)) ?_
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (euclidean_zero_tail_inclusion_continuous n k).continuousAt
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).symm
    (chartAt (EuclideanSpace ℝ (Fin n)) x)
    (chartAt (EuclideanSpace ℝ (Fin (n + k))) (euclidean_zero_tail_inclusion n k x))
    (mem_chart_source _ x)
    (mem_chart_source _ _)
    (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.chart_mem_maximalAtlas (euclidean_zero_tail_inclusion n k x))
  intro y hy
  simp [euclidean_zero_tail_inclusion_eq_finAddEquivProd]
