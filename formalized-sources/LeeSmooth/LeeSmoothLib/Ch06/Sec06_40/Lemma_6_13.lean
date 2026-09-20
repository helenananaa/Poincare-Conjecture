import Mathlib
import LeeSmoothLib.Ch06.Sec06_38.Proposition_6_8
import LeeSmoothLib.Ch06.Sec06_39.Corollary_6_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the statement surface was matched against the repository's Euclidean embedded-submanifold
-- statements and mathlib's `Manifold.IsSmoothEmbedding` / `Manifold.IsImmersion` APIs.

universe uE uH

/-- The last coordinate index of `Fin N`, defined under the positivity hypothesis `0 < N`. -/
private def lastCoordinateIndex {N : ℕ} (hN : 0 < N) : Fin N :=
  ⟨N - 1, Nat.sub_lt hN (Nat.succ_pos 0)⟩

/-- The order-preserving embedding of the first `N - 1` coordinates into `Fin N`. -/
private def dropLastCoordinateEmbedding {N : ℕ} (hN : 0 < N) :
    Fin (N - 1) → Fin N :=
  fun i ↦ ⟨i.1, lt_trans i.2 (Nat.sub_lt hN (Nat.succ_pos 0))⟩

/-- The oblique projection from `ℝ^N` onto the last-coordinate-zero hyperplane, written in
`Fin`-coordinates and taken along the line spanned by `v`. For vectors `v` with nonzero last
coordinate, this is the projection whose kernel is `ℝ v`. -/
def obliqueProjectionToLastHyperplane {N : ℕ} (hN : 0 < N)
    (v : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin (N - 1)) :=
  fun x ↦
    (EuclideanSpace.equiv (Fin (N - 1)) ℝ).symm fun i ↦
      x (dropLastCoordinateEmbedding hN i) -
        (x (lastCoordinateIndex hN) / v (lastCoordinateIndex hN)) *
          v (dropLastCoordinateEmbedding hN i)

/-- The oblique projection along `v` is given coordinatewise by subtracting the unique multiple of
`v` that kills the last coordinate. -/
theorem obliqueProjectionToLastHyperplane_apply {N : ℕ} (hN : 0 < N)
    (v x : EuclideanSpace ℝ (Fin N)) (i : Fin (N - 1)) :
    obliqueProjectionToLastHyperplane hN v x i =
      x (dropLastCoordinateEmbedding hN i) -
        (x (lastCoordinateIndex hN) / v (lastCoordinateIndex hN)) *
          v (dropLastCoordinateEmbedding hN i) := by
  -- The coordinate formula is exactly the definition of `obliqueProjectionToLastHyperplane`.
  rfl

section

variable {N : ℕ}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {J : ModelWithCorners ℝ E H}
variable {M : Set (EuclideanSpace ℝ (Fin N))}
variable [ChartedSpace H M] [IsManifold J ∞ M]

/-- A direction whose associated oblique projection to the last-coordinate-zero hyperplane is
defined and restricts to an injective immersion on `M`. -/
class ObliqueProjectionDirectionRestrictsToInjectiveImmersion
    (hN : 0 < N) (v : EuclideanSpace ℝ (Fin N)) : Prop where
  lastCoordinate_ne_zero :
    v (lastCoordinateIndex hN) ≠ 0
  injective :
    Function.Injective (fun p : M ↦ obliqueProjectionToLastHyperplane hN v p.1)
  isImmersion :
    Manifold.IsImmersion
      J
      (𝓡 (N - 1))
      ∞
      (fun p : M ↦ obliqueProjectionToLastHyperplane hN v p.1)

/-- The nonvanishing last-coordinate condition attached to a good oblique projection direction. -/
theorem obliqueProjectionDirectionRestrictsToInjectiveImmersion_fact_lastCoordinate_ne_zero
    (hN : 0 < N) (v : EuclideanSpace ℝ (Fin N))
    [hv :
      ObliqueProjectionDirectionRestrictsToInjectiveImmersion (J := J) (M := M) hN v] :
    Fact (v (lastCoordinateIndex hN) ≠ 0) := by
  -- The class stores the nonvanishing last-coordinate hypothesis as one of its fields.
  exact ⟨hv.lastCoordinate_ne_zero⟩

namespace Lemma613

open Bundle MeasureTheory Set

/-- The continuous-linear version of dropping the last coordinate from `ℝ^(K+1)`. -/
private noncomputable def dropLastCoordinatesCLM (K : ℕ) :
    EuclideanSpace ℝ (Fin (K + 1)) →L[ℝ] EuclideanSpace ℝ (Fin K) :=
  ((↑(EuclideanSpace.equiv (Fin K) ℝ).symm :
      (Fin K → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin K)).comp
    ((ContinuousLinearMap.pi
      (fun i : Fin K ↦ ContinuousLinearMap.proj (Fin.castSucc i))).comp
      (↑(EuclideanSpace.equiv (Fin (K + 1)) ℝ) :
        EuclideanSpace ℝ (Fin (K + 1)) →L[ℝ] (Fin (K + 1) → ℝ))))

/-- Evaluation at the last coordinate as a continuous linear functional. -/
private noncomputable def lastCoordinateCLM (K : ℕ) :
    EuclideanSpace ℝ (Fin (K + 1)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (Fin.last K)).comp
    (↑(EuclideanSpace.equiv (Fin (K + 1)) ℝ) :
      EuclideanSpace ℝ (Fin (K + 1)) →L[ℝ] (Fin (K + 1) → ℝ))

/-- The first `K` coordinates of an ambient direction. -/
private noncomputable def truncatedDirection (K : ℕ)
    (v : EuclideanSpace ℝ (Fin (K + 1))) : EuclideanSpace ℝ (Fin K) :=
  (EuclideanSpace.equiv (Fin K) ℝ).symm fun i ↦ v (Fin.castSucc i)

/-- The oblique projection along `v`, as a continuous linear map. -/
private noncomputable def obliqueProjectionCLM (K : ℕ)
    (v : EuclideanSpace ℝ (Fin (K + 1))) :
    EuclideanSpace ℝ (Fin (K + 1)) →L[ℝ] EuclideanSpace ℝ (Fin K) :=
  dropLastCoordinatesCLM K -
    (lastCoordinateCLM K).smulRight ((v (Fin.last K))⁻¹ • truncatedDirection K v)

private lemma obliqueProjectionCLM_apply (K : ℕ)
    (v x : EuclideanSpace ℝ (Fin (K + 1))) (i : Fin K) :
    obliqueProjectionCLM K v x i =
      x (Fin.castSucc i) - (x (Fin.last K) / v (Fin.last K)) * v (Fin.castSucc i) := by
  simp [obliqueProjectionCLM, dropLastCoordinatesCLM, lastCoordinateCLM,
    truncatedDirection, div_eq_mul_inv, sub_eq_add_neg, mul_comm, mul_assoc]

private lemma obliqueProjection_eq_clm (K : ℕ)
    (v x : EuclideanSpace ℝ (Fin (K + 1))) :
    obliqueProjectionToLastHyperplane (Nat.succ_pos K) v x =
      obliqueProjectionCLM K v x := by
  ext i
  rw [obliqueProjectionCLM_apply]
  rfl

/-- The kernel of the oblique projection is the line spanned by its direction. -/
private lemma obliqueProjectionCLM_eq_zero_iff_smul (K : ℕ)
    (v : EuclideanSpace ℝ (Fin (K + 1))) (hv : v (Fin.last K) ≠ 0)
    {x : EuclideanSpace ℝ (Fin (K + 1))} :
    obliqueProjectionCLM K v x = 0 ↔ ∃ a : ℝ, x = a • v := by
  constructor
  · intro hx
    refine ⟨x (Fin.last K) / v (Fin.last K), ?_⟩
    ext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · have hcoord : obliqueProjectionCLM K v x i = 0 := by
        simpa using congrArg (fun y ↦ y i) hx
      rw [obliqueProjectionCLM_apply] at hcoord
      exact (sub_eq_zero.mp hcoord).trans (by simp [smul_eq_mul, mul_comm])
    · simp [smul_eq_mul]
      field_simp [hv]
  · rintro ⟨a, rfl⟩
    ext i
    rw [obliqueProjectionCLM_apply]
    simp [smul_eq_mul, hv]

/-- The map whose range contains every scalar multiple of every secant of `M`. -/
private noncomputable def secantDirectionMap
    (K : ℕ) (M : Set (EuclideanSpace ℝ (Fin (K + 1)))) :
    ℝ × (M × M) → EuclideanSpace ℝ (Fin (K + 1)) :=
  fun z ↦ z.1 • ((z.2.1 : EuclideanSpace ℝ (Fin (K + 1))) - z.2.2)

private lemma secantDirectionMap_contMDiff
    {K : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H}
    {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
    [ChartedSpace H M] [IsManifold J ∞ M]
    (hM : Manifold.IsSmoothEmbedding J (𝓡 (K + 1)) ∞
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1)))) :
    ContMDiff ((𝓘(ℝ)).prod (J.prod J)) (𝓡 (K + 1)) ∞
      (secantDirectionMap K M) := by
  have hx :
      ContMDiff ((𝓘(ℝ)).prod (J.prod J)) (𝓡 (K + 1)) ∞
        (fun z : ℝ × (M × M) ↦
          (z.2.1 : EuclideanSpace ℝ (Fin (K + 1)))) :=
    hM.contMDiff.comp (contMDiff_fst.comp contMDiff_snd)
  have hy :
      ContMDiff ((𝓘(ℝ)).prod (J.prod J)) (𝓡 (K + 1)) ∞
        (fun z : ℝ × (M × M) ↦
          (z.2.2 : EuclideanSpace ℝ (Fin (K + 1)))) :=
    hM.contMDiff.comp (contMDiff_snd.comp contMDiff_snd)
  change ContMDiff ((𝓘(ℝ)).prod (J.prod J)) (𝓡 (K + 1)) ∞
    (fun z : ℝ × (M × M) ↦
      z.1 • ((z.2.1 : EuclideanSpace ℝ (Fin (K + 1))) - z.2.2))
  exact contMDiff_fst.smul (hx.sub hy)

/-- The ambient derivative-vector map on the full tangent bundle. -/
private noncomputable def ambientTangentVector
    {K : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] (J : ModelWithCorners ℝ E H)
    {M : Set (EuclideanSpace ℝ (Fin (K + 1)))} [ChartedSpace H M]
    (F : M → EuclideanSpace ℝ (Fin (K + 1))) :
    TangentBundle J M → EuclideanSpace ℝ (Fin (K + 1)) :=
  fun u ↦ (tangentMap J (𝓡 (K + 1)) F u).2

private lemma ambientTangentVector_apply
    {K : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    {M : Set (EuclideanSpace ℝ (Fin (K + 1)))} [ChartedSpace H M]
    {F : M → EuclideanSpace ℝ (Fin (K + 1))}
    (x : M) (u : TangentSpace J x) :
    ambientTangentVector J F ⟨x, u⟩ = mfderiv J (𝓡 (K + 1)) F x u := by
  simpa [ambientTangentVector] using
    (tangentMap_snd (I := J) (I' := 𝓡 (K + 1)) (f := F) (x := x) (X := u))

private lemma ambientTangentVector_contMDiff
    {K : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
    {J : ModelWithCorners ℝ E H}
    {M : Set (EuclideanSpace ℝ (Fin (K + 1)))} [ChartedSpace H M] [IsManifold J ∞ M]
    {F : M → EuclideanSpace ℝ (Fin (K + 1))}
    (hF : ContMDiff J (𝓡 (K + 1)) ∞ F) :
    ContMDiff J.tangent (𝓡 (K + 1)) ∞ (ambientTangentVector J F) := by
  simpa [ambientTangentVector, Function.comp] using!
    (contMDiff_snd_tangentBundle_modelSpace
      (EuclideanSpace ℝ (Fin (K + 1))) (𝓡 (K + 1))).comp
      (hF.contMDiff_tangentMap (m := ∞) le_rfl)

/-- Hausdorffness of the tangent bundle, supplied explicitly because Mathlib does not register it
as a global instance for an arbitrary model with corners. -/
private lemma tangentBundle_t2Space
    {K : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    {M : Set (EuclideanSpace ℝ (Fin (K + 1)))} [ChartedSpace H M]
    [IsManifold J ∞ M] [T2Space M] :
    T2Space (TangentBundle J M) := by
  let TM := TangentBundle J M
  refine ⟨?_⟩
  intro p q hpq
  by_cases hproj : p.1 = q.1
  · let e := trivializationAt E (TangentSpace J) p.1
    have hpSource : p ∈ e.source := by
      simpa [e] using
        (mem_trivializationAt_proj_source (F := E) (E := TangentSpace J) (x := p))
    have hqSource : q ∈ e.source := by
      simpa [e, hproj] using
        (mem_trivializationAt_proj_source (F := E) (E := TangentSpace J) (x := q))
    let ps : e.source := ⟨p, hpSource⟩
    let qs : e.source := ⟨q, hqSource⟩
    have hpsq : ps ≠ qs := by
      intro h
      exact hpq (congrArg Subtype.val h)
    let _ : T2Space e.baseSet := inferInstance
    let _ : T2Space E := inferInstance
    let _ : T2Space (e.baseSet × E) := inferInstance
    let _ : T2Space e.source := e.sourceHomeomorphBaseSetProd.symm.t2Space
    simpa [ps, qs] using
      (separated_by_isOpenEmbedding
        (f := ((↑) : e.source → TM)) e.open_source.isOpenEmbedding_subtypeVal hpsq)
  · exact separated_by_continuous
      (f := fun z : TM ↦ z.1)
      (FiberBundle.continuous_proj E (TangentSpace J)) hproj

/-- Second countability of the tangent bundle, obtained from a countable chart cover. -/
private lemma tangentBundle_secondCountable
    {K : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    {M : Set (EuclideanSpace ℝ (Fin (K + 1)))} [ChartedSpace H M]
    [IsManifold J ∞ M] [SecondCountableTopology M] :
    SecondCountableTopology (TangentBundle J M) := by
  let TM := TangentBundle J M
  obtain ⟨s, hsCountable, hsCover⟩ :=
    countable_cover_nhds (fun x : M ↦ chart_source_mem_nhds H x)
  let U : s → Set TM :=
    fun x ↦ (trivializationAt E (TangentSpace J) (x : M)).source
  have hUOpen : ∀ x : s, IsOpen (U x) := by
    intro x
    exact (trivializationAt E (TangentSpace J) (x : M)).open_source
  have hUCover : ⋃ x : s, U x = univ := by
    ext p
    constructor
    · intro
      simp
    · intro hp
      rcases Set.mem_iUnion.1 (by
          simpa [hsCover] using hp : p.1 ∈ ⋃ x : s, (chartAt H (x : M)).source) with ⟨x, hx⟩
      refine Set.mem_iUnion.2 ⟨x, ?_⟩
      change p ∈ (trivializationAt E (TangentSpace J) (x : M)).source
      exact (Trivialization.mem_source _).2 hx
  have hUSecondCountable : ∀ x : s, SecondCountableTopology (U x) := by
    intro x
    let e := trivializationAt E (TangentSpace J) (x : M)
    let _ : SecondCountableTopology e.baseSet := inferInstance
    let _ : SecondCountableTopology E := inferInstance
    let _ : SecondCountableTopology (e.baseSet × E) := inferInstance
    exact e.sourceHomeomorphBaseSetProd.secondCountableTopology
  let _ : Countable s := hsCountable.to_subtype
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hUOpen hUCover

/-- The standard inclusion of the last-coordinate-zero hyperplane. -/
private noncomputable def lastHyperplaneInclusionCLM (K : ℕ) :
    EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1)) :=
  ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := K) (m := 1)).symm :
      (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (K + 1))).toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin K)) (EuclideanSpace ℝ (Fin 1)))

private lemma lastHyperplaneInclusionCLM_last (K : ℕ)
    (x : EuclideanSpace ℝ (Fin K)) :
    lastHyperplaneInclusionCLM K x (Fin.last K) = 0 := by
  simp [lastHyperplaneInclusionCLM]

private lemma lastHyperplaneInclusionCLM_castSucc (K : ℕ)
    (x : EuclideanSpace ℝ (Fin K)) (i : Fin K) :
    lastHyperplaneInclusionCLM K x (Fin.castSucc i) = x i := by
  simp [lastHyperplaneInclusionCLM]

private lemma hasMeasureZeroInManifold_union
    {A B : Set (EuclideanSpace ℝ (Fin N))}
    (hA : has_measure_zero_in_manifold (𝓡 N) A)
    (hB : has_measure_zero_in_manifold (𝓡 N) B) :
    has_measure_zero_in_manifold (𝓡 N) (A ∪ B) := by
  intro μ hμ e he
  simpa [union_inter_distrib_right, image_union] using
    measure_union_null (hA μ hμ e he) (hB μ hμ e he)

end Lemma613

/-- Lemma 6.13: let `M ⊆ ℝ^N` be an ordinary (boundaryless) smooth submanifold, presented as a
smoothly embedded subtype. If `N > 2 * dim(M) + 1`, then the set of vectors with nonzero last
coordinate for which the corresponding oblique projection to the last-coordinate-zero hyperplane
restricts to an injective immersion on `M` is dense in `ℝ^N`. -/
theorem dense_oblique_projection_directions_restrict_to_injective_immersion
    [J.Boundaryless]
    (hN : 0 < N)
    (hM :
      Manifold.IsSmoothEmbedding
        J
        (𝓡 N)
        ∞
        (Subtype.val : M → EuclideanSpace ℝ (Fin N)))
    (hdim : 2 * Module.finrank ℝ E + 1 < N) :
    Dense
      {v : EuclideanSpace ℝ (Fin N) |
        ObliqueProjectionDirectionRestrictsToInjectiveImmersion (J := J) (M := M) hN v} := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hhN : hN = Nat.succ_pos K := Subsingleton.elim _ _
  subst hN
  let secantBad : Set (EuclideanSpace ℝ (Fin (K + 1))) :=
    Set.range (Lemma613.secantDirectionMap K M)
  let tangentBad : Set (EuclideanSpace ℝ (Fin (K + 1))) :=
    Set.range
      (Lemma613.ambientTangentVector J
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))))
  let hyperplaneBad : Set (EuclideanSpace ℝ (Fin (K + 1))) :=
    Set.range (Lemma613.lastHyperplaneInclusionCLM K)
  have hdimSecant :
      Module.finrank ℝ (ℝ × (E × E)) <
        Module.finrank ℝ (EuclideanSpace ℝ (Fin (K + 1))) := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
    omega
  have hSecantNull :
      has_measure_zero_in_manifold (𝓡 (K + 1)) secantBad := by
    exact
      range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt
        (I := (𝓘(ℝ)).prod (J.prod J))
        (J := 𝓡 (K + 1))
        (F := Lemma613.secantDirectionMap K M)
        (Lemma613.secantDirectionMap_contMDiff hM)
        hdimSecant
  let _ : T2Space (TangentBundle J M) := Lemma613.tangentBundle_t2Space
  let _ : SecondCountableTopology (TangentBundle J M) :=
    Lemma613.tangentBundle_secondCountable
  have hdimTangent :
      Module.finrank ℝ (E × E) <
        Module.finrank ℝ (EuclideanSpace ℝ (Fin (K + 1))) := by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega
  have hTangentNull :
      has_measure_zero_in_manifold (𝓡 (K + 1)) tangentBad := by
    exact
      range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt
        (I := J.tangent)
        (J := 𝓡 (K + 1))
        (F := Lemma613.ambientTangentVector J
          (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))))
        (Lemma613.ambientTangentVector_contMDiff hM.contMDiff)
        hdimTangent
  have hdimHyperplane :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin K)) <
        Module.finrank ℝ (EuclideanSpace ℝ (Fin (K + 1))) := by
    simp only [finrank_euclideanSpace_fin]
    omega
  have hHyperplaneNull :
      has_measure_zero_in_manifold (𝓡 (K + 1)) hyperplaneBad := by
    exact
      range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt
        (I := 𝓡 K)
        (J := 𝓡 (K + 1))
        (F := Lemma613.lastHyperplaneInclusionCLM K)
        (Lemma613.lastHyperplaneInclusionCLM K).contMDiff
        hdimHyperplane
  have hBadNull :
      has_measure_zero_in_manifold (𝓡 (K + 1))
        (secantBad ∪ (tangentBad ∪ hyperplaneBad)) :=
    Lemma613.hasMeasureZeroInManifold_union hSecantNull
      (Lemma613.hasMeasureZeroInManifold_union hTangentNull hHyperplaneNull)
  have hDenseBadComplement :
      Dense ((secantBad ∪ (tangentBad ∪ hyperplaneBad))ᶜ :
        Set (EuclideanSpace ℝ (Fin (K + 1)))) :=
    has_measure_zero_in_manifold.dense_compl hBadNull
  refine hDenseBadComplement.mono ?_
  intro v hvGood
  have hvParts : v ∉ secantBad ∧ v ∉ tangentBad ∧ v ∉ hyperplaneBad := by
    simpa only [Set.mem_compl_iff, Set.mem_union, not_or] using hvGood
  have hvLast : v (Fin.last K) ≠ 0 := by
    intro h
    apply hvParts.2.2
    refine ⟨Lemma613.dropLastCoordinatesCLM K v, ?_⟩
    ext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · rw [Lemma613.lastHyperplaneInclusionCLM_castSucc]
      simp [Lemma613.dropLastCoordinatesCLM]
    · rw [Lemma613.lastHyperplaneInclusionCLM_last, h]
  refine
    { lastCoordinate_ne_zero := hvLast
      injective := ?_
      isImmersion := ?_ }
  · intro p q hpq
    let P := Lemma613.obliqueProjectionCLM K v
    have hpq' : P p.1 = P q.1 := by
      simpa [P, Lemma613.obliqueProjection_eq_clm] using hpq
    have hkernel : P (p.1 - q.1) = 0 := by
      rw [map_sub, hpq', sub_self]
    rcases (Lemma613.obliqueProjectionCLM_eq_zero_iff_smul K v hvLast).1 hkernel with ⟨a, ha⟩
    by_contra hpne
    have ha0 : a ≠ 0 := by
      intro haZero
      apply hpne
      apply Subtype.ext
      have hval : p.1 - q.1 = 0 := by simpa [haZero] using ha
      exact sub_eq_zero.mp hval
    apply hvParts.1
    refine ⟨(a⁻¹, (p, q)), ?_⟩
    change a⁻¹ • (p.1 - q.1) = v
    rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  · let P := Lemma613.obliqueProjectionCLM K v
    let F : M → EuclideanSpace ℝ (Fin K) := fun p ↦ P p.1
    have hFCont : ContMDiff J (𝓡 K) ∞ F := by
      simpa [F, P, Function.comp] using! P.contMDiff.comp hM.contMDiff
    have hValInj :
        ∀ x : M, Function.Injective
          (mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x) :=
      (Manifold.is_immersion_iff_forall_injective_mfderiv hM.contMDiff).1 hM.isImmersion
    have hFImmersion : Manifold.IsImmersion J (𝓡 K) ∞ F := by
      refine (Manifold.is_immersion_iff_forall_injective_mfderiv hFCont).2 ?_
      intro x u w huw
      have hComp :
          mfderiv J (𝓡 K) F x =
            P.comp (mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x) := by
        simpa [F, P, Function.comp] using!
          (mfderiv_comp (x := x) (g := P) (f := (Subtype.val : M → _))
            (P.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
            (hM.contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
      have hu :
          mfderiv J (𝓡 K) F x u =
            P (mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x u) := by
        simpa [P] using! congrArg (fun L ↦ L u) hComp
      have hw :
          mfderiv J (𝓡 K) F x w =
            P (mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x w) := by
        simpa [P] using! congrArg (fun L ↦ L w) hComp
      have hkernelEq :
          P
            (mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x u -
              mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x w) = 0 := by
        have hsub : mfderiv J (𝓡 K) F x u - mfderiv J (𝓡 K) F x w = 0 := by
          simp [huw]
        calc
          P
              (mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x u -
                mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x w) =
              P (mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x u) -
                P (mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x w) := by
                exact P.map_sub _ _
          _ = mfderiv J (𝓡 K) F x u - mfderiv J (𝓡 K) F x w := by
                rw [← hu, ← hw]
          _ = 0 := hsub
      have hkernel :
          P (mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x (u - w)) = 0 := by
        simpa [map_sub] using hkernelEq
      rcases (Lemma613.obliqueProjectionCLM_eq_zero_iff_smul K v hvLast).1 hkernel with
        ⟨a, ha⟩
      have hAmbientZero :
          mfderiv J (𝓡 (K + 1)) (Subtype.val : M → _) x (u - w) = 0 := by
        by_cases ha0 : a = 0
        · simpa [ha0] using ha
        · exfalso
          apply hvParts.2.1
          refine ⟨⟨x, a⁻¹ • (u - w)⟩, ?_⟩
          rw [Lemma613.ambientTangentVector_apply, map_smul, ha, smul_smul,
            inv_mul_cancel₀ ha0, one_smul]
      have hdiff : u - w = 0 := by
        apply hValInj x
        simpa using hAmbientZero
      exact sub_eq_zero.mp hdiff
    simpa [F, P, Lemma613.obliqueProjection_eq_clm] using hFImmersion

end
