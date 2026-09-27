import PoincareConjecture.ProofContract.Refinement20260927.SmoothRetractionModel
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedSmoothRetractionForm
open PoincareConjecture.ProofContract.Refinement20260927
theorem smooth_retraction_form : SmoothRetractionFormStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  open PoincareConjecture.ProofContract.V1 in
  open scoped Manifold ContDiff Topology BigOperators Bundle in
  intro N g n R
  let E := ApproxAmbient n
  let I := 𝓘(ℝ, E)
  let J := 𝓡 3
  let basisVec (i : Fin n) : E :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm (Pi.single i (1 : ℝ))
  let coord (i : Fin n) : E →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
      (φ := fun _ : Fin n => ℝ) i).comp
      (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap
  let pairForm (i j : Fin n) : E →L[ℝ] E →L[ℝ] ℝ :=
    ContinuousLinearMap.smulRight (coord i) (coord j)
  let f : E → N := R.localRetract
  have hRetract (p : N) : f (R.embed p) = p := by
    calc
      f (R.embed p) = R.retract ⟨R.embed p, R.contains p⟩ :=
        R.agrees (R.embed p) (R.contains p)
      _ = p := R.retract_embed p
  letI : Riemannian.HasMetric J N := ⟨g⟩
  letI : Bundle.RiemannianBundle (TangentSpace J : N → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : ∀ x : N, NormedAddCommGroup (TangentSpace J x) :=
    fun x => (g.toRiemannianMetric.toCore x).toNormedAddCommGroupOfTopology
      (g.toRiemannianMetric.continuousAt x) (g.toRiemannianMetric.isVonNBounded x)
  letI : ∀ x : N, InnerProductSpace ℝ (TangentSpace J x) :=
    fun x => InnerProductSpace.ofCoreOfTopology (g.toRiemannianMetric.toCore x)
      (g.toRiemannianMetric.continuousAt x) (g.toRiemannianMetric.isVonNBounded x)
  letI : IsContMDiffRiemannianBundle J 0
      (EuclideanSpace ℝ (Fin 3)) (TangentSpace J : N → Type _) :=
    ⟨⟨g.inner, g.contMDiff.of_le (by simp), by intro x v w; rfl⟩⟩
  let localCoeff (i j : Fin n) (x : E) : ℝ :=
    inner ℝ (mfderivWithin I J f R.domain x (basisVec i))
      (mfderivWithin I J f R.domain x (basisVec j))
  let coeff (i j : Fin n) (p : N) : ℝ := localCoeff i j (R.embed p)

  have hTan : ContMDiffOn I.tangent J.tangent 0
      (tangentMapWithin I J f R.domain)
      (Bundle.TotalSpace.proj ⁻¹' R.domain) := by
    exact R.smooth_localRetract.contMDiffOn_tangentMapWithin
      (m := 0) (by simp) R.open_domain.uniqueMDiffOn
  let sourceSection (i : Fin n) (x : E) : TangentBundle I E := ⟨x, basisVec i⟩
  have hsourceSection (i : Fin n) :
      ContMDiff I I.tangent 0 (sourceSection i) := by
    let V : ∀ x : E, TangentSpace I x := fun _ => basisVec i
    have hV : ContDiffOn ℝ (0 : WithTop ℕ∞) V Set.univ :=
      contDiff_const.contDiffOn
    have hT : ContMDiffOn I I.tangent (0 : WithTop ℕ∞) (T% V) Set.univ :=
      (contMDiffOn_vectorSpace_iff_contDiffOn (𝕜 := ℝ) (E := E) (V := V)).2 hV
    rw [← contMDiffOn_univ]
    have heq : sourceSection i = T% V := by
      funext x
      rfl
    rw [heq]
    exact hT
  let targetSection (i : Fin n) (x : E) : TangentBundle J N :=
    ⟨f x, mfderivWithin I J f R.domain x (basisVec i)⟩
  have htargetSection (i : Fin n) :
      ContMDiffOn I J.tangent 0 (targetSection i) R.domain := by
    have hcomp : ContMDiffOn I J.tangent 0
        (tangentMapWithin I J f R.domain ∘ sourceSection i) R.domain := by
      apply hTan.comp (hsourceSection i).contMDiffOn
      intro x hx
      simpa [sourceSection] using hx
    have heq : targetSection i = tangentMapWithin I J f R.domain ∘ sourceSection i := by
      funext x
      simp [targetSection, sourceSection, tangentMapWithin]
    rw [heq]
    exact hcomp
  have hlocalCoeff (i j : Fin n) :
      ContMDiffOn I (𝓘(ℝ, ℝ)) 0 (localCoeff i j) R.domain := by
    have h := (htargetSection i).inner_bundle (htargetSection j)
    simpa [localCoeff, targetSection] using h
  have hcoeff (i j : Fin n) : Continuous (coeff i j) := by
    change Continuous (localCoeff i j ∘ R.embed)
    apply continuousOn_univ.mp
    exact (hlocalCoeff i j).continuousOn.comp
      (R.embed.continuous.continuousOn : ContinuousOn R.embed Set.univ)
      (by intro p hp; exact R.contains p)

  let form (p : N) : E →L[ℝ] E →L[ℝ] ℝ :=
    ∑ i : Fin n, ∑ j : Fin n, coeff i j p • pairForm i j
  have hform : Continuous form := by
    dsimp [form]
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    exact (hcoeff i j).smul continuous_const

  refine ⟨form, hform, ?_⟩
  intro p v w
  let q : E := R.embed p
  let dEmbed : TangentSpace J p →L[ℝ] E := mfderiv J I R.embed p
  let dRetract := mfderiv I J f q
  have hq : q ∈ R.domain := R.contains p
  have hwithin : mfderivWithin I J f R.domain q = mfderiv I J f q :=
    mfderivWithin_of_mem_nhds (R.open_domain.mem_nhds hq)
  have hcoeffAt (i j : Fin n) :
      coeff i j p = g.metricInner p (dRetract (basisVec i)) (dRetract (basisVec j)) := by
    dsimp [coeff, localCoeff]
    have hwithin' : mfderivWithin I J f R.domain (R.embed p) =
        mfderiv I J f (R.embed p) := by simpa [q] using hwithin
    rw [hwithin']
    conv_rhs =>
      arg 1
      rw [← hRetract p]
    rfl
  have hdecomp (x : TangentSpace I q) :
      (∑ i : Fin n, coord i x • basisVec i) = x := by
    change (∑ i : Fin n, coord i (show E from x) • basisVec i) = (show E from x)
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    simp only [map_sum, map_smul]
    ext j
    simp [coord, basisVec, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Finset.sum_ite_eq, Pi.single_apply]
    rfl
  have hdRetract (x : TangentSpace I q) :
      dRetract x = ∑ i : Fin n, coord i x • dRetract (basisVec i) := by
    calc
      dRetract x = dRetract (∑ i : Fin n, coord i x • basisVec i) := by rw [hdecomp]
      _ = ∑ i : Fin n, dRetract (coord i x • basisVec i) := map_sum _ _ _
      _ = ∑ i : Fin n, coord i x • dRetract (basisVec i) := by simp
  have hmetricExpansion (x y : TangentSpace I q) :
      g.metricInner p (dRetract x) (dRetract y) =
        ∑ i : Fin n, ∑ j : Fin n, coeff i j p * (coord i x * coord j y) := by
    calc
      g.metricInner p (dRetract x) (dRetract y) =
          ∑ i : Fin n, coord i x *
            g.metricInner p (dRetract (basisVec i)) (dRetract y) := by
        rw [hdRetract x]
        simp only [Riemannian.RiemannianMetric.metricInner_apply,
          map_sum, map_smul, smul_eq_mul,
          ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      _ = ∑ i : Fin n, coord i x *
            (∑ j : Fin n, coord j y *
              g.metricInner p (dRetract (basisVec i)) (dRetract (basisVec j))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hdRetract y]
        simp only [Riemannian.RiemannianMetric.metricInner_apply,
          map_sum, map_smul, smul_eq_mul,
          ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      _ = ∑ i : Fin n, ∑ j : Fin n,
            coeff i j p * (coord i x * coord j y) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← hcoeffAt]
        ring
  have hRetMD (p : N) : MDifferentiableAt I J f (R.embed p) := by
    exact (R.smooth_localRetract (R.embed p) (R.contains p)).mdifferentiableWithinAt
      (by simp) |>.mdifferentiableAt (R.open_domain.mem_nhds (R.contains p))
  have hEmbedMD (p : N) : MDifferentiableAt J I R.embed p :=
    (R.smooth_embed.mdifferentiable (by simp)) p
  have hchainV : dRetract (dEmbed v) = v := by
    have h := mfderiv_comp_apply (f := R.embed) p (hRetMD p) (hEmbedMD p) v
    have hfun : f ∘ R.embed = id := by
      funext x
      exact hRetract x
    rw [hfun, mfderiv_id] at h
    exact h.symm
  have hchainW : dRetract (dEmbed w) = w := by
    have h := mfderiv_comp_apply (f := R.embed) p (hRetMD p) (hEmbedMD p) w
    have hfun : f ∘ R.embed = id := by
      funext x
      exact hRetract x
    rw [hfun, mfderiv_id] at h
    exact h.symm
  have hformApply (x y : E) :
      form p x y =
        ∑ i : Fin n, ∑ j : Fin n, coeff i j p * (coord i x * coord j y) := by
    simp [form, pairForm]
  calc
    g.metricInner p v w = g.metricInner p (dRetract (dEmbed v)) (dRetract (dEmbed w)) := by
      rw [hchainV, hchainW]
    _ = form p (dEmbed v) (dEmbed w) := by
      rw [hmetricExpansion, ← hformApply]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedSmoothRetractionForm
