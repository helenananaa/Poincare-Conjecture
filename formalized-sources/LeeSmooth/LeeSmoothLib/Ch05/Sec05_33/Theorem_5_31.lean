import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
import LeeSmoothLib.Ch05.Sec05_31.Definition_5_31_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch06.Sec06_39.Corollary_6_11
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH'

section UniquenessOfSubmanifoldStructures

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J (⊤ : WithTop ℕ∞) S]
variable [IsEmbeddedSubmanifold I J S]

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement shape
-- was chosen from the local `IsEmbeddedSubmanifold` / `ImmersedSubmanifold` API in Chapter 5.
-- Proof sketch: use Corollary 5.30 to view the alternative inclusion as a smooth map
-- `S̃ → S`, check from injectivity of the ambient differential that this map is an immersion, and
-- then apply the global rank theorem to obtain a diffeomorphism.
/-- Compatibility form of Theorem 5.31: if `S ⊆ M` carries an embedded submanifold structure and
an immersed presentation `T` of the same subset is already known to carry the topology induced by
its ambient inclusion, then `T` is diffeomorphic to `S` through that inclusion.

This is a useful intermediate result, but it is not the textbook uniqueness theorem: `hTind`
already assumes the missing topological compatibility. -/
theorem immersed_submanifold_structure_unique_of_same_carrier_of_inducing
    (T : Manifold.ImmersedSubmanifold I M) (hT : T.carrier = S)
    (hTind : Topology.IsInducing T.inclusion) :
    ∃ Φ : T ≃ₘ⟮modelWithCornersSelf 𝕜 T.ModelSpace, J⟯ S,
      ∀ x : T, (Φ x : M) = T.inclusion x := by
  let hS : IsEmbeddedSubmanifold I J S := inferInstance
  let toS : T → S := fun x ↦ ⟨T.inclusion x, by
    rw [← hT]
    exact Set.mem_range_self x⟩
  let fromS : S → T := fun y ↦ Classical.choose (by
    have hy : (y : M) ∈ T.carrier := by simpa [hT] using y.property
    simpa [Manifold.ImmersedSubmanifold.carrier] using hy)
  have hfromS : ∀ y : S, T.inclusion (fromS y) = y := by
    intro y
    exact Classical.choose_spec (by
      have hy : (y : M) ∈ T.carrier := by simpa [hT] using y.property
      simpa [Manifold.ImmersedSubmanifold.carrier] using hy)
  let e : T ≃ S :=
    { toFun := toS
      invFun := fromS
      left_inv := fun x ↦ T.inclusion_injective (by simpa [toS] using hfromS (toS x))
      right_inv := fun y ↦ Subtype.ext (by simpa [toS] using hfromS y) }
  have he_to : (Subtype.val : S → M) ∘ e = T.inclusion := by
    rfl
  have he_inv : T.inclusion ∘ e.symm = (Subtype.val : S → M) := by
    funext y
    exact hfromS y
  have he_cont : Continuous (e : T → S) := by
    refine hS.isSmoothEmbedding_subtype_val.isEmbedding.isInducing.continuous_iff.2 ?_
    rw [he_to]
    exact T.inclusion_isImmersion.contMDiff.continuous
  have he_inv_cont : Continuous (e.symm : S → T) := by
    refine hTind.continuous_iff.2 ?_
    rw [he_inv]
    exact hS.isSmoothEmbedding_subtype_val.contMDiff.continuous
  have he_smooth : ContMDiff (modelWithCornersSelf 𝕜 T.ModelSpace) J ⊤ e := by
    refine (ContMDiff.iff_comp_isImmersion
      hS.isSmoothEmbedding_subtype_val.isImmersion).2 ⟨he_cont, ?_⟩
    rw [he_to]
    exact T.inclusion_isImmersion.contMDiff
  have he_inv_smooth : ContMDiff J (modelWithCornersSelf 𝕜 T.ModelSpace) ⊤ e.symm := by
    refine (ContMDiff.iff_comp_isImmersion T.inclusion_isImmersion).2 ⟨he_inv_cont, ?_⟩
    rw [he_inv]
    exact hS.isSmoothEmbedding_subtype_val.contMDiff
  let Φ : T ≃ₘ⟮modelWithCornersSelf 𝕜 T.ModelSpace, J⟯ S :=
    { toEquiv := e
      contMDiff_toFun := he_smooth.of_le (by simp)
      contMDiff_invFun := he_inv_smooth.of_le (by simp) }
  refine ⟨Φ, ?_⟩
  intro x
  rfl

end UniquenessOfSubmanifoldStructures

noncomputable section

open MeasureTheory

/-- Reuse an immersion's chart normal forms at a lower differentiability index. -/
private lemma isImmersion_of_le_531
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    {I₁ : ModelWithCorners 𝕜 E₁ H₁} [IsManifold I₁ (⊤ : WithTop ℕ∞) M₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {H₂ : Type*} [TopologicalSpace H₂]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    {I₂ : ModelWithCorners 𝕜 E₂ H₂} [IsManifold I₂ (⊤ : WithTop ℕ∞) M₂]
    {n m : WithTop ℕ∞} {f : M₁ → M₂} (hmn : m ≤ n)
    (hf : Manifold.IsImmersion I₁ I₂ n f) :
    Manifold.IsImmersion I₁ I₂ m f := by
  let hComp := hf.complement
  let hCompImm := hf.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I₁) (M := M₁) hmn)
      hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I₂) (M := M₂) hmn)
      hx.codChart_mem_maximalAtlas

section OrdinaryRealUniquenessOfSubmanifoldStructures

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J (⊤ : WithTop ℕ∞) S]
variable [IsEmbeddedSubmanifold I J S]

/-- Theorem 5.31 (ordinary finite-dimensional real manifolds): an embedded submanifold structure
on `S` is unique among Hausdorff, second-countable immersed realizations with the same carrier.

The hypotheses restore the textbook convention that manifolds are finite-dimensional real,
Hausdorff, and second-countable.  They cannot simply be dropped in the formal interface: give the
underlying set of `ℝ` the uncountable discrete topology and the zero-dimensional smooth structure.
Its identity map into the ordinary real line is an injective immersion with the same carrier, but
the two topologies are not homeomorphic.

The source and embedded model spaces are not assumed finite-dimensional separately.  In the
nonempty case their immersion normal forms into the finite-dimensional ambient model imply that
automatically. -/
theorem immersed_submanifold_structure_unique_of_same_carrier
    (T : Manifold.ImmersedSubmanifold I M) [T2Space T] [SecondCountableTopology T]
    (hT : T.carrier = S) :
    ∃ Φ : T ≃ₘ⟮modelWithCornersSelf ℝ T.ModelSpace, J⟯ S,
      ∀ x : T, (Φ x : M) = T.inclusion x := by
  classical
  let hS : IsEmbeddedSubmanifold I J S := inferInstance
  let toS : T → S := fun x ↦ ⟨T.inclusion x, by
    rw [← hT]
    exact Set.mem_range_self x⟩
  let fromS : S → T := fun y ↦ Classical.choose (by
    have hy : (y : M) ∈ T.carrier := by simpa [hT] using y.property
    simpa [Manifold.ImmersedSubmanifold.carrier] using hy)
  have hfromS : ∀ y : S, T.inclusion (fromS y) = y := by
    intro y
    exact Classical.choose_spec (by
      have hy : (y : M) ∈ T.carrier := by simpa [hT] using y.property
      simpa [Manifold.ImmersedSubmanifold.carrier] using hy)
  let e : T ≃ S :=
    { toFun := toS
      invFun := fromS
      left_inv := fun x ↦ T.inclusion_injective (by simpa [toS] using hfromS (toS x))
      right_inv := fun y ↦ Subtype.ext (by simpa [toS] using hfromS y) }
  have he_to : (Subtype.val : S → M) ∘ e = T.inclusion := by
    rfl
  have he_cont : Continuous (e : T → S) := by
    refine hS.isSmoothEmbedding_subtype_val.isEmbedding.isInducing.continuous_iff.2 ?_
    rw [he_to]
    exact T.inclusion_isImmersion.contMDiff.continuous
  have hTImmInf :
      Manifold.IsImmersion (modelWithCornersSelf ℝ T.ModelSpace) I ∞ T.inclusion :=
    isImmersion_of_le_531 (by simp) T.inclusion_isImmersion
  have hSImmInf : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
    isImmersion_of_le_531 (by simp) hS.isSmoothEmbedding_subtype_val.isImmersion
  have he_smooth : ContMDiff (modelWithCornersSelf ℝ T.ModelSpace) J ∞ e := by
    refine (ContMDiff.iff_comp_isImmersion
      hSImmInf).2 ⟨he_cont, ?_⟩
    rw [he_to]
    exact hTImmInf.contMDiff
  by_cases hEmpty : IsEmpty T
  · letI : IsEmpty T := hEmpty
    let Φ : T ≃ₘ⟮modelWithCornersSelf ℝ T.ModelSpace, J⟯ S :=
      { toEquiv := e
        contMDiff_toFun := fun x ↦ isEmptyElim x
        contMDiff_invFun := fun y ↦ isEmptyElim (e.symm y) }
    exact ⟨Φ, fun x ↦ isEmptyElim x⟩
  · letI : Nonempty T := not_isEmpty_iff.mp hEmpty
    let p₀ : T := Classical.arbitrary T
    let hTImm := T.inclusion_isImmersion.isImmersionAt p₀
    let _ : FiniteDimensional ℝ (T.ModelSpace × hTImm.complement) :=
      FiniteDimensional.of_injective hTImm.equiv.toLinearMap hTImm.equiv.injective
    letI : FiniteDimensional ℝ T.ModelSpace :=
      FiniteDimensional.of_injective
        (ContinuousLinearMap.inl ℝ T.ModelSpace hTImm.complement).toLinearMap
        LinearMap.inl_injective
    let q₀ : S := e p₀
    let hSImm := hS.isSmoothEmbedding_subtype_val.isImmersion.isImmersionAt q₀
    let _ : FiniteDimensional ℝ (E' × hSImm.complement) :=
      FiniteDimensional.of_injective hSImm.equiv.toLinearMap hSImm.equiv.injective
    letI : FiniteDimensional ℝ E' :=
      FiniteDimensional.of_injective
        (ContinuousLinearMap.inl ℝ E' hSImm.complement).toLinearMap
        LinearMap.inl_injective
    have he_mfderiv_injective :
        ∀ p : T, Function.Injective
          (mfderiv (modelWithCornersSelf ℝ T.ModelSpace) J e p) := by
      intro p
      have he_md :
          MDifferentiableAt (modelWithCornersSelf ℝ T.ModelSpace) J e p :=
        he_smooth.mdifferentiable (by simp) p
      have hval_md : MDifferentiableAt J I (Subtype.val : S → M) (e p) :=
        hSImmInf.contMDiff.mdifferentiable (by simp) (e p)
      have hcomp : Function.Injective
          ((mfderiv J I (Subtype.val : S → M) (e p)).comp
            (mfderiv (modelWithCornersSelf ℝ T.ModelSpace) J e p)) := by
        rw [← mfderiv_comp p hval_md he_md, he_to]
        exact hTImmInf.mfderiv_injective p
      intro v w hvw
      apply hcomp
      simp only [ContinuousLinearMap.comp_apply]
      rw [hvw]
    have hdim_le : Module.finrank ℝ T.ModelSpace ≤ Module.finrank ℝ E' := by
      let p : T := Classical.arbitrary T
      letI : FiniteDimensional ℝ (TangentSpace (modelWithCornersSelf ℝ T.ModelSpace) p) := by
        change FiniteDimensional ℝ T.ModelSpace
        infer_instance
      letI : FiniteDimensional ℝ (TangentSpace J (e p)) := by
        change FiniteDimensional ℝ E'
        infer_instance
      have hle := LinearMap.finrank_le_finrank_of_injective (he_mfderiv_injective p)
      change Module.finrank ℝ T.ModelSpace ≤ Module.finrank ℝ E' at hle
      exact hle
    have hdim : Module.finrank ℝ T.ModelSpace = Module.finrank ℝ E' := by
      apply Nat.le_antisymm hdim_le
      by_contra hnot
      have hlt : Module.finrank ℝ T.ModelSpace < Module.finrank ℝ E' := by omega
      letI : MeasurableSpace E' := borel E'
      letI : BorelSpace E' := ⟨rfl⟩
      have hzero : has_measure_zero_in_manifold J (Set.range (e : T → S)) :=
        range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt he_smooth hlt
      let μ : Measure E' := (Module.finBasis ℝ E').addHaar
      have htarget_zero : μ ((extChartAt J q₀).target) = 0 := by
        have hz := hzero μ inferInstance (chartAt H' q₀)
          (IsManifold.chart_mem_maximalAtlas q₀)
        rw [e.surjective.range_eq, Set.univ_inter,
          ← (chartAt H' q₀).extend_target_eq_image_source] at hz
        exact hz
      have hq₀_interior :
          (extChartAt J q₀) q₀ ∈ interior ((extChartAt J q₀).target) := by
        exact J.isInteriorPoint_iff.mp BoundarylessManifold.isInteriorPoint
      have htarget_pos : 0 < μ ((extChartAt J q₀).target) :=
        (isOpen_interior.measure_pos μ ⟨_, hq₀_interior⟩).trans_le
          (measure_mono interior_subset)
      exact (ne_of_gt htarget_pos) htarget_zero
    have he_local :
        IsLocalDiffeomorph (modelWithCornersSelf ℝ T.ModelSpace) J ∞ e := by
      intro p
      letI : NormedAddCommGroup
          (TangentSpace (modelWithCornersSelf ℝ T.ModelSpace) p) := by
        change NormedAddCommGroup T.ModelSpace
        infer_instance
      letI : NormedSpace ℝ
          (TangentSpace (modelWithCornersSelf ℝ T.ModelSpace) p) := by
        change NormedSpace ℝ T.ModelSpace
        infer_instance
      letI : CompleteSpace
          (TangentSpace (modelWithCornersSelf ℝ T.ModelSpace) p) := by
        change CompleteSpace T.ModelSpace
        infer_instance
      letI : FiniteDimensional ℝ
          (TangentSpace (modelWithCornersSelf ℝ T.ModelSpace) p) := by
        change FiniteDimensional ℝ T.ModelSpace
        infer_instance
      letI : NormedAddCommGroup (TangentSpace J (e p)) := by
        change NormedAddCommGroup E'
        infer_instance
      letI : NormedSpace ℝ (TangentSpace J (e p)) := by
        change NormedSpace ℝ E'
        infer_instance
      letI : CompleteSpace (TangentSpace J (e p)) := by
        change CompleteSpace E'
        infer_instance
      letI : FiniteDimensional ℝ (TangentSpace J (e p)) := by
        change FiniteDimensional ℝ E'
        infer_instance
      have hinj := he_mfderiv_injective p
      have hdim_tangent :
          Module.finrank ℝ (TangentSpace (modelWithCornersSelf ℝ T.ModelSpace) p) =
            Module.finrank ℝ (TangentSpace J (e p)) := by
        change Module.finrank ℝ T.ModelSpace = Module.finrank ℝ E'
        exact hdim
      have hsurj : Function.Surjective
          (mfderiv (modelWithCornersSelf ℝ T.ModelSpace) J e p) :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim_tangent).mp hinj
      have hInv :
          (mfderiv (modelWithCornersSelf ℝ T.ModelSpace) J e p).IsInvertible :=
        ContinuousLinearMap.isInvertible_of_bijective hinj hsurj
      exact isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible
        (I := modelWithCornersSelf ℝ T.ModelSpace) (J := J) (n := ∞) (by simp)
        BoundarylessManifold.isInteriorPoint he_smooth hInv
    let Φ : T ≃ₘ⟮modelWithCornersSelf ℝ T.ModelSpace, J⟯ S :=
      he_local.diffeomorphOfBijective e.bijective
    refine ⟨Φ, ?_⟩
    intro x
    change (e x : M) = T.inclusion x
    rfl

end OrdinaryRealUniquenessOfSubmanifoldStructures
