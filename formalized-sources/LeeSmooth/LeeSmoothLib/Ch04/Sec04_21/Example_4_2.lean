import Mathlib
import LeeSmoothLib.Ch03.Sec03_17.Definition_3_17_extra_1
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_25.Proposition_4_28
-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the statement
-- shapes were fixed from the local smooth-submersion API in `Proposition_4_28`, the curve-velocity
-- API in `Definition_3_17_extra_1`, and the canonical mathlib tangent-bundle owners.

noncomputable section

open Bundle
open scoped ContDiff Manifold Topology

universe uι uE uH uM

section FiniteProductProjections

variable {ι : Type uι} [Fintype ι]
variable {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
variable {H : ι → Type uH} [∀ i, TopologicalSpace (H i)]
variable {I : ∀ i, ModelWithCorners ℝ (E i) (H i)}
variable {M : ι → Type uM} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  [∀ i, IsManifold (I i) ∞ (M i)]
  [IsManifold (ModelWithCorners.pi I) ∞ (∀ i, M i)]

/-- Helper for Example 4.2: a point lies in the range of `ModelWithCorners.pi I` exactly when
each coordinate lies in the range of the corresponding factor model. -/
lemma mem_range_modelWithCornersPi_iff {y : ∀ j, E j} :
    y ∈ Set.range (ModelWithCorners.pi I) ↔ ∀ j, y j ∈ Set.range (I j) := by
  constructor
  · rintro ⟨x, rfl⟩ j
    exact ⟨x j, rfl⟩
  · intro hy
    choose x hx using hy
    refine ⟨x, ?_⟩
    ext j
    exact hx j

/-- Helper for Example 4.2: the product chart target is the product of the factor chart
targets. -/
lemma mem_piChartAt_target_iff (p : ∀ j, M j) {y : ∀ j, E j} :
    (ModelWithCorners.pi I).symm y ∈ (chartAt (H := ModelPi H) p).target ↔
      ∀ j, (I j).symm (y j) ∈ (chartAt (H j) (p j)).target := by
  constructor
  · intro hy j
    change ((PartialEquiv.pi (fun i => (I i).toPartialEquiv)).symm y) j ∈
      (chartAt (H j) (p j)).target
    exact hy j (by simp)
  · intro hy j hj
    change ((PartialEquiv.pi (fun i => (I i).toPartialEquiv)).symm y) j ∈
      (chartAt (H j) (p j)).target
    rw [PartialEquiv.pi_symm_apply]
    exact hy j

/-- Helper for Example 4.2: the target of the finite-product extended chart is the
coordinatewise product of the factor extended-chart targets. -/
lemma mem_extChartAt_pi_target_iff (p : ∀ j, M j) {y : ∀ j, E j} :
    y ∈ (extChartAt (ModelWithCorners.pi I) p).target ↔
      ∀ j, y j ∈ (extChartAt (I j) (p j)).target := by
  rw [extChartAt_target]
  constructor
  · rintro ⟨hyChart, hyRange⟩ j
    have hyChartj : (I j).symm (y j) ∈ (chartAt (H j) (p j)).target :=
      (mem_piChartAt_target_iff (I := I) p).1 hyChart j
    have hyRangej : y j ∈ Set.range (I j) :=
      (mem_range_modelWithCornersPi_iff (I := I)).1 hyRange j
    simpa [extChartAt_target] using And.intro hyRangej hyChartj
  · intro hy
    refine ⟨(mem_piChartAt_target_iff (I := I) p).2 ?_,
      (mem_range_modelWithCornersPi_iff (I := I)).2 ?_⟩
    · intro j
      exact (hy j).2
    · intro j
      simpa using (hy j).1

/-- Helper for Example 4.2: the inverse of the finite-product extended chart acts
coordinatewise on each factor. -/
lemma extChartAt_pi_symm_apply (p : ∀ j, M j) (y : ∀ j, E j) (j : ι) :
    ((extChartAt (ModelWithCorners.pi I) p).symm y) j =
      (extChartAt (I j) (p j)).symm (y j) :=
  rfl

/-- Helper for Example 4.2: the finite-product extended chart sends `p` to the tuple of its
factor extended-chart coordinates. -/
lemma extChartAt_pi_apply (p : ∀ j, M j) (j : ι) :
    extChartAt (ModelWithCorners.pi I) p p j = extChartAt (I j) (p j) (p j) :=
  rfl

/-- Helper for Example 4.2: the `j`-th coordinate projection on a finite product manifold has
manifold derivative `ContinuousLinearMap.proj j`. -/
lemma hasMFDerivAt_piProjection (p : ∀ j, M j) (j : ι) :
    HasMFDerivAt (ModelWithCorners.pi I) (I j) (fun x : ∀ l, M l ↦ x j) p
      (ContinuousLinearMap.proj j) := by
  refine ⟨continuous_apply j |>.continuousAt, ?_⟩
  have hChart :
      ∀ᶠ y in 𝓝[Set.range (ModelWithCorners.pi I)] extChartAt (ModelWithCorners.pi I) p p,
        (extChartAt (I j) (p j) ∘ (fun x : ∀ l, M l ↦ x j) ∘
          (extChartAt (ModelWithCorners.pi I) p).symm) y = y j := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := ModelWithCorners.pi I) p] with y hy
    have hyj : y j ∈ (extChartAt (I j) (p j)).target :=
      (mem_extChartAt_pi_target_iff (I := I) p).1 hy j
    calc
      (extChartAt (I j) (p j) ∘ (fun x : ∀ l, M l ↦ x j) ∘
          (extChartAt (ModelWithCorners.pi I) p).symm) y
          = extChartAt (I j) (p j) (((extChartAt (ModelWithCorners.pi I) p).symm y) j) := rfl
      _ = extChartAt (I j) (p j) ((extChartAt (I j) (p j)).symm (y j)) := by
        rw [extChartAt_pi_symm_apply (I := I)]
      _ = y j := (extChartAt (I j) (p j)).right_inv hyj
  apply HasFDerivWithinAt.congr_of_eventuallyEq
    (hasFDerivWithinAt_apply j (extChartAt (ModelWithCorners.pi I) p p)
      (Set.range (ModelWithCorners.pi I)))
    hChart
  rw [extChartAt_pi_apply (I := I)]
  exact (extChartAt (I j) (p j)).right_inv <|
    (extChartAt (I j) (p j)).map_source (mem_extChartAt_source (I := I j) (p j))

/-- Helper for Example 4.2: the manifold derivative of the `j`-th coordinate projection is
the coordinate projection on tangent spaces. -/
lemma mfderiv_piProjection (p : ∀ j, M j) (j : ι) :
    mfderiv (ModelWithCorners.pi I) (I j) (fun x : ∀ l, M l ↦ x j) p =
      ContinuousLinearMap.proj j :=
  (hasMFDerivAt_piProjection (I := I) p j).mfderiv

/-- Example 4.2 (1): for a finite product of smooth manifolds, each coordinate projection is a
smooth submersion. -/
theorem finite_product_projection_isSmoothSubmersion (i : ι) :
    Manifold.IsSmoothSubmersion (ModelWithCorners.pi I) (I i) (fun x : ∀ j, M j ↦ x i) := by
  refine ⟨?_, ?_⟩
  · intro x
    have hx := (contMDiff_id : ContMDiff (ModelWithCorners.pi I) (ModelWithCorners.pi I) ∞ id) x
    rw [contMDiffAt_iff_target] at hx ⊢
    constructor
    · exact (continuous_apply i).continuousAt.comp hx.1
    · exact contMDiffAt_pi_space.1 hx.2 i
  · intro x
    rw [mfderiv_piProjection]
    intro v
    letI : DecidableEq ι := Classical.decEq ι
    refine ⟨Pi.single i (show E i from v), ?_⟩
    change (Pi.single i (show E i from v)) i = v
    exact Pi.single_eq_same i _

end FiniteProductProjections

/-- The projection of `ℝ^(n+k)` onto its first `n` coordinates. -/
def euclidean_first_projection (n k : ℕ) :
    EuclideanSpace ℝ (Fin (n + k)) → EuclideanSpace ℝ (Fin n) :=
  fun x ↦ WithLp.toLp 2 fun i ↦ x (Fin.castLE (Nat.le_add_right n k) i)

/-- The first-coordinate projection is computed by evaluating the source vector on the corresponding
head index. -/
theorem euclidean_first_projection_apply {n k : ℕ} (x : EuclideanSpace ℝ (Fin (n + k)))
    (i : Fin n) :
    euclidean_first_projection n k x i = x (Fin.castLE (Nat.le_add_right n k) i) :=
  rfl

/-- Helper for Example 4.2: the Euclidean first-coordinate projection is a continuous linear
map. -/
def euclidean_first_projectionCLM (n k : ℕ) :
    EuclideanSpace ℝ (Fin (n + k)) →L[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun := euclidean_first_projection n k
  map_add' := by
    intro x y
    ext i
    simp [euclidean_first_projection]
  map_smul' := by
    intro c x
    ext i
    simp [euclidean_first_projection]
  cont := by
    have hcoord :
        Continuous fun x : EuclideanSpace ℝ (Fin (n + k)) ↦
          fun i : Fin n ↦ x (Fin.castLE (Nat.le_add_right n k) i) :=
      continuous_pi fun i ↦
        PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + k) ↦ ℝ)
          (Fin.castLE (Nat.le_add_right n k) i)
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp hcoord

/-- Helper for Example 4.2: padding a vector in `ℝ^n` by `k` zeros recovers a right inverse of
the first-coordinate projection. -/
def euclidean_first_inclusion (n k : ℕ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + k)) :=
  fun y ↦ WithLp.toLp 2 fun i ↦
    if h : (i : ℕ) < n then y ⟨i, h⟩ else 0

/-- Helper for Example 4.2: the zero-tail inclusion is a right inverse of the first-coordinate
projection. -/
theorem euclidean_first_projection_inclusion (n k : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    euclidean_first_projection n k (euclidean_first_inclusion n k y) = y := by
  ext i
  simp [euclidean_first_projection, euclidean_first_inclusion, Fin.val_castLE]

/-- Example 4.2 (2): the projection `ℝ^(n+k) → ℝ^n` onto the first `n` coordinates is a smooth
submersion. -/
theorem euclidean_first_projection_isSmoothSubmersion (n k : ℕ) :
    Manifold.IsSmoothSubmersion (𝓡 (n + k)) (𝓡 n) (euclidean_first_projection n k) := by
  let L := euclidean_first_projectionCLM n k
  refine ⟨?_, ?_⟩
  · simpa [L, euclidean_first_projectionCLM] using
      (L.contMDiff : ContMDiff (𝓡 (n + k)) (𝓡 n) ∞ L)
  · intro x
    rw [mfderiv_eq_fderiv]
    have hderiv : fderiv ℝ (euclidean_first_projection n k) x = L := by
      simpa [L, euclidean_first_projectionCLM] using (L.hasFDerivAt).fderiv
    rw [hderiv]
    intro y
    exact ⟨euclidean_first_inclusion n k y, euclidean_first_projection_inclusion n k y⟩

section CurveImmersionCriterion

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Example 4.2 (3): for a smooth curve on a parameter interval, pointwise injectivity of the
within-interval manifold derivative is equivalent to nonvanishing within-interval velocity. This is
the formal interval version of Lee's criterion that `γ` is a smooth immersion exactly when
`γ'(t) ≠ 0` for all parameters. -/
theorem smooth_curve_injective_mfderivWithin_iff_forall_velocityWithin_ne_zero
    {J : Set ℝ} {γ : ℝ → M} (_hJ : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ) J t)
    (_hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ J) :
    (∀ t ∈ J, Function.Injective (mfderivWithin 𝓘(ℝ) I γ J t)) ↔
      ∀ t ∈ J, curve_velocityWithin I γ J t ≠ 0 := by
  constructor
  · intro hinj t ht hvel
    have h1 :
        curve_velocityWithin I γ J t =
          (mfderivWithin 𝓘(ℝ) I γ J t) (1 : TangentSpace 𝓘(ℝ) t) :=
      rfl
    have h0 : (mfderivWithin 𝓘(ℝ) I γ J t) (0 : TangentSpace 𝓘(ℝ) t) = 0 :=
      map_zero _
    have h10 :
        (mfderivWithin 𝓘(ℝ) I γ J t) (1 : TangentSpace 𝓘(ℝ) t) =
          (mfderivWithin 𝓘(ℝ) I γ J t) (0 : TangentSpace 𝓘(ℝ) t) := by
      simp [h1.symm, hvel, h0]
    have : (1 : TangentSpace 𝓘(ℝ) t) = (0 : TangentSpace 𝓘(ℝ) t) :=
      hinj t ht h10
    exact one_ne_zero (show (1 : ℝ) = 0 from this)
  · intro hvel t ht a b hab
    have h1 :
        curve_velocityWithin I γ J t =
          (mfderivWithin 𝓘(ℝ) I γ J t) (1 : TangentSpace 𝓘(ℝ) t) :=
      rfl
    have hsub : (mfderivWithin 𝓘(ℝ) I γ J t) (a - b) = 0 := by
      simp [map_sub, hab]
    let δ : ℝ := a - b
    have hδ1 : a - b = δ • (1 : TangentSpace 𝓘(ℝ) t) := by
      change (a - b : ℝ) = δ * (1 : ℝ)
      simp [δ]
    have hsmul : δ • curve_velocityWithin I γ J t = 0 := by
      rw [h1, ← map_smul, ← hδ1]
      exact hsub
    by_cases hδ : δ = 0
    · exact sub_eq_zero.mp (show (a - b : ℝ) = 0 from hδ)
    · have : curve_velocityWithin I γ J t = 0 := by
        have := congrArg (fun v ↦ δ⁻¹ • v) hsmul
        simpa [smul_smul, inv_mul_cancel₀ hδ] using this
      exact (hvel t ht this).elim

end CurveImmersionCriterion

section TangentBundleProjection

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Example 4.2 (4): the tangent-bundle projection `TM → M`, with the canonical smooth structure
on `TM`, is a smooth submersion. -/
theorem tangentBundle_projection_isSmoothSubmersion :
    Manifold.IsSmoothSubmersion I.tangent I (TotalSpace.proj : TangentBundle I M → M) := by
  refine ⟨Bundle.contMDiff_proj (TangentSpace I), ?_⟩
  intro p
  let e := trivializationAt E (TangentSpace I) p.proj
  let c : E := (e p).2
  let σ : M → TangentBundle I M := fun y ↦ e.toOpenPartialHomeomorph.symm (y, c)
  have hp_base : p.proj ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p.proj
  have hσp : σ p.proj = p := e.symm_apply_mk_proj (e.mem_source.2 hp_base)
  have hσ_proj : ∀ y ∈ e.baseSet, (σ y).proj = y := fun y hy ↦ e.proj_symm_apply' hy
  have hσ_nhds : TotalSpace.proj ∘ σ =ᶠ[𝓝 p.proj] id := by
    filter_upwards [e.open_baseSet.mem_nhds hp_base] with y hy
    exact hσ_proj y hy
  have hσ_cont : ContMDiffAt I I.tangent ∞ σ p.proj := by
    rw [Bundle.contMDiffAt_totalSpace]
    constructor
    · refine contMDiffAt_id.congr_of_eventuallyEq ?_
      filter_upwards [e.open_baseSet.mem_nhds hp_base] with y hy
      exact (hσ_proj y hy).symm
    · have hfib :
          (fun y : M ↦ (trivializationAt E (TangentSpace I) (σ p.proj).proj (σ y)).2) =ᶠ[𝓝 p.proj]
            fun _ ↦ c := by
        rw [hσp]
        filter_upwards [e.open_baseSet.mem_nhds hp_base] with y hy
        change (e (σ y)).2 = c
        simp [σ, e.apply_symm_apply' hy]
      exact (contMDiffAt_const (c := c)).congr_of_eventuallyEq hfib
  have hπ_mdiff :
      MDifferentiableAt I.tangent I (TotalSpace.proj : TangentBundle I M → M) p :=
    (Bundle.contMDiff_proj (TangentSpace I)).mdifferentiable (by simp : (∞ : ℕ∞ω) ≠ 0) p
  have hσ_mdiff : MDifferentiableAt I I.tangent σ p.proj :=
    hσ_cont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hcomp :
      mfderiv I I (TotalSpace.proj ∘ σ) p.proj =
        (mfderiv I.tangent I (TotalSpace.proj : TangentBundle I M → M) (σ p.proj)).comp
          (mfderiv I I.tangent σ p.proj) :=
    mfderiv_comp p.proj (by rw [hσp]; exact hπ_mdiff) hσ_mdiff
  have hid : mfderiv I I (TotalSpace.proj ∘ σ) p.proj = ContinuousLinearMap.id ℝ _ := by
    rw [hσ_nhds.mfderiv_eq]
    exact mfderiv_id
  intro v
  refine ⟨mfderiv I I.tangent σ p.proj v, ?_⟩
  have hgoal :
      (mfderiv I.tangent I (TotalSpace.proj : TangentBundle I M → M) (σ p.proj))
        (mfderiv I I.tangent σ p.proj v) = v := by
    have hv := DFunLike.congr_fun (hid.symm.trans hcomp) v
    erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hv
    exact hv.symm
  rw [← hσp]
  exact hgoal

end TangentBundleProjection

/-- The torus-of-revolution parameterization from Example 4.2 (d). -/
def torus_revolution_map : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) :=
  fun p ↦
    let u := p 0
    let v := p 1
    WithLp.toLp 2
      ![(2 + Real.cos (2 * Real.pi * u)) * Real.cos (2 * Real.pi * v),
        (2 + Real.cos (2 * Real.pi * u)) * Real.sin (2 * Real.pi * v),
        Real.sin (2 * Real.pi * u)]

/-- The explicit coordinate formula for `torus_revolution_map`. -/
theorem torus_revolution_map_apply (p : EuclideanSpace ℝ (Fin 2)) :
    torus_revolution_map p =
      WithLp.toLp 2
        ![(2 + Real.cos (2 * Real.pi * p 0)) * Real.cos (2 * Real.pi * p 1),
          (2 + Real.cos (2 * Real.pi * p 0)) * Real.sin (2 * Real.pi * p 1),
          Real.sin (2 * Real.pi * p 0)] :=
  rfl

/-- The standard torus of revolution in `ℝ^3`, written as the level set
`(sqrt (x^2 + y^2) - 2)^2 + z^2 = 1`. -/
def torus_revolution_surface : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - 2) ^ 2 + x 2 ^ 2 = 1}

/-- Membership in `torus_revolution_surface` is the standard torus equation in Cartesian
coordinates. -/
theorem mem_torus_revolution_surface_iff {x : EuclideanSpace ℝ (Fin 3)} :
    x ∈ torus_revolution_surface ↔
      (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - 2) ^ 2 + x 2 ^ 2 = 1 :=
  Iff.rfl

/-- Helper for Example 4.2: the scalar factor `2 + cos θ` is strictly positive. -/
lemma torus_revolution_factor_cos_pos (θ : ℝ) : 0 < (2 : ℝ) + Real.cos θ := by
  nlinarith [Real.neg_one_le_cos θ]

/-- Helper for Example 4.2: a unit complex number has squared modulus one. -/
lemma complex_norm_eq_one_of_re_sq_add_im_sq {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp [h]

/-- Helper for Example 4.2: the torus parameterization is smooth as a map of Euclidean
spaces. -/
theorem torus_revolution_map_contMDiff :
    ContMDiff (𝓡 2) (𝓡 3) ∞ torus_revolution_map := by
  rw [contMDiff_iff_contDiff]
  refine (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 3 ↦ ℝ)).comp ?_
  rw [contDiff_pi]
  intro i
  fin_cases i
  · have h0 :
        ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) ↦ Real.cos (2 * Real.pi * p 1)) :=
      Real.contDiff_cos.comp
        (contDiff_const.mul
          (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 1)))
    have h1 :
        ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) ↦ (2 : ℝ) + Real.cos (2 * Real.pi * p 0)) :=
      contDiff_const.add
        (Real.contDiff_cos.comp
          (contDiff_const.mul
            (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 0))))
    simpa [torus_revolution_map] using h1.mul h0
  · have h0 :
        ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) ↦ Real.sin (2 * Real.pi * p 1)) :=
      Real.contDiff_sin.comp
        (contDiff_const.mul
          (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 1)))
    have h1 :
        ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) ↦ (2 : ℝ) + Real.cos (2 * Real.pi * p 0)) :=
      contDiff_const.add
        (Real.contDiff_cos.comp
          (contDiff_const.mul
            (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 0))))
    simpa [torus_revolution_map] using h1.mul h0
  · simpa [torus_revolution_map] using!
      Real.contDiff_sin.comp
        (contDiff_const.mul
          (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 0)))

/-- Helper for Example 4.2: the first coordinate of the torus parameterization has the expected
derivative. -/
lemma torus_revolution_first_coord_hasFDerivAt (p : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt
      ((fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 : ℝ) + Real.cos (2 * Real.pi * q 0)) *
        (Real.cos ∘ fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 1))
      (((2 : ℝ) + Real.cos (2 * Real.pi * p 0)) •
          (-Real.sin (2 * Real.pi * p 1) •
            ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 :
              EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ))) +
        (Real.cos ∘ fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 1) p •
          (-Real.sin (2 * Real.pi * p 0) •
            ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 :
              EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)))) p := by
  have h0coord :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ q 0)
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 0
  have h1coord :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ q 1)
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 1
  have h0scale :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 0)
        ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0)) p :=
    h0coord.const_mul (2 * Real.pi)
  have h1scale :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 1)
        ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1)) p :=
    h1coord.const_mul (2 * Real.pi)
  have hcos0 :
      HasFDerivAt
        (Real.cos ∘ fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 0)
        (-Real.sin (2 * Real.pi * p 0) • ((2 * Real.pi) •
          (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0))) p :=
    (Real.hasDerivAt_cos (2 * Real.pi * p 0)).comp_hasFDerivAt p h0scale
  have hcos1 :
      HasFDerivAt
        (Real.cos ∘ fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 1)
        (-Real.sin (2 * Real.pi * p 1) • ((2 * Real.pi) •
          (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1))) p :=
    (Real.hasDerivAt_cos (2 * Real.pi * p 1)).comp_hasFDerivAt p h1scale
  have hfactor :
      HasFDerivAt
        (fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 : ℝ) + Real.cos (2 * Real.pi * q 0))
        (-Real.sin (2 * Real.pi * p 0) • ((2 * Real.pi) •
          (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0))) p :=
    hcos0.const_add (2 : ℝ)
  exact hfactor.mul hcos1

/-- Helper for Example 4.2: the second coordinate of the torus parameterization has the expected
derivative. -/
lemma torus_revolution_second_coord_hasFDerivAt (p : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt
      ((fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 : ℝ) + Real.cos (2 * Real.pi * q 0)) *
        (Real.sin ∘ fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 1))
      (((2 : ℝ) + Real.cos (2 * Real.pi * p 0)) •
          (Real.cos (2 * Real.pi * p 1) •
            ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 :
              EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ))) +
        (Real.sin ∘ fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 1) p •
          (-Real.sin (2 * Real.pi * p 0) •
            ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 :
              EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)))) p := by
  have h0coord :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ q 0)
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 0
  have h1coord :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ q 1)
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 1
  have h0scale :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 0)
        ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0)) p :=
    h0coord.const_mul (2 * Real.pi)
  have h1scale :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 1)
        ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1)) p :=
    h1coord.const_mul (2 * Real.pi)
  have hcos0 :
      HasFDerivAt
        (Real.cos ∘ fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 0)
        (-Real.sin (2 * Real.pi * p 0) • ((2 * Real.pi) •
          (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0))) p :=
    (Real.hasDerivAt_cos (2 * Real.pi * p 0)).comp_hasFDerivAt p h0scale
  have hsin1 :
      HasFDerivAt
        (Real.sin ∘ fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 1)
        (Real.cos (2 * Real.pi * p 1) • ((2 * Real.pi) •
          (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1))) p :=
    (Real.hasDerivAt_sin (2 * Real.pi * p 1)).comp_hasFDerivAt p h1scale
  have hfactor :
      HasFDerivAt
        (fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 : ℝ) + Real.cos (2 * Real.pi * q 0))
        (-Real.sin (2 * Real.pi * p 0) • ((2 * Real.pi) •
          (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0))) p :=
    hcos0.const_add (2 : ℝ)
  exact hfactor.mul hsin1

/-- Helper for Example 4.2: the third coordinate of the torus parameterization has the expected
derivative. -/
lemma torus_revolution_third_coord_hasFDerivAt (p : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt
      (fun q : EuclideanSpace ℝ (Fin 2) ↦ Real.sin (2 * Real.pi * q 0))
      ((2 * Real.pi * Real.cos (2 * Real.pi * p 0)) •
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) p := by
  have h0coord :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ q 0)
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 0
  have h0scale :
      HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 0)
        ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0)) p :=
    h0coord.const_mul (2 * Real.pi)
  have hsin := (Real.hasDerivAt_sin (2 * Real.pi * p 0)).comp_hasFDerivAt p h0scale
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using! hsin

/-- Helper for Example 4.2: the derivative of the torus parameterization has the expected
coordinate formula. -/
theorem torus_revolution_map_fderiv_apply (p v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ torus_revolution_map p v =
      WithLp.toLp 2
        ![
          -((2 * Real.pi) * Real.sin (2 * Real.pi * p 0) * Real.cos (2 * Real.pi * p 1)) * v 0 -
            ((2 : ℝ) + Real.cos (2 * Real.pi * p 0)) * (2 * Real.pi) *
              Real.sin (2 * Real.pi * p 1) * v 1,
          -((2 * Real.pi) * Real.sin (2 * Real.pi * p 0) * Real.sin (2 * Real.pi * p 1)) * v 0 +
            ((2 : ℝ) + Real.cos (2 * Real.pi * p 0)) * (2 * Real.pi) *
              Real.cos (2 * Real.pi * p 1) * v 1,
          (2 * Real.pi) * Real.cos (2 * Real.pi * p 0) * v 0
        ] := by
  let L0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    ((2 : ℝ) + Real.cos (2 * Real.pi * p 0)) •
        (-Real.sin (2 * Real.pi * p 1) •
          ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 :
            EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ))) +
      (Real.cos ∘ fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 1) p •
        (-Real.sin (2 * Real.pi * p 0) •
          ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 :
            EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)))
  let L1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    ((2 : ℝ) + Real.cos (2 * Real.pi * p 0)) •
        (Real.cos (2 * Real.pi * p 1) •
          ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 :
            EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ))) +
      (Real.sin ∘ fun q : EuclideanSpace ℝ (Fin 2) ↦ (2 * Real.pi) * q 1) p •
        (-Real.sin (2 * Real.pi * p 0) •
          ((2 * Real.pi) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 :
            EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)))
  let L2 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    ((2 * Real.pi) * Real.cos (2 * Real.pi * p 0)) •
      (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
  have hpi :
      HasFDerivAt
        (fun q : EuclideanSpace ℝ (Fin 2) ↦
          ![
            ((2 : ℝ) + Real.cos (2 * Real.pi * q 0)) * Real.cos (2 * Real.pi * q 1),
            ((2 : ℝ) + Real.cos (2 * Real.pi * q 0)) * Real.sin (2 * Real.pi * q 1),
            Real.sin (2 * Real.pi * q 0)
          ])
        (ContinuousLinearMap.pi ![L0, L1, L2]) p := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · simpa [L0] using! torus_revolution_first_coord_hasFDerivAt p
    · simpa [L1] using! torus_revolution_second_coord_hasFDerivAt p
    · simpa [L2] using! torus_revolution_third_coord_hasFDerivAt p
  have htoLp :
      HasFDerivAt
        (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm.toContinuousLinearMap)
        ![
          ((2 : ℝ) + Real.cos (2 * Real.pi * p 0)) * Real.cos (2 * Real.pi * p 1),
          ((2 : ℝ) + Real.cos (2 * Real.pi * p 0)) * Real.sin (2 * Real.pi * p 1),
          Real.sin (2 * Real.pi * p 0)
        ] :=
    PiLp.hasFDerivAt_toLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) _
  have hImm :
      HasFDerivAt torus_revolution_map
        (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.pi ![L0, L1, L2])) p := by
    simpa [torus_revolution_map] using! htoLp.comp p hpi
  rw [hImm.fderiv]
  have htuple :
      ![L0 v, L1 v, L2 v] =
        ![
          -((2 * Real.pi) * Real.sin (2 * Real.pi * p 0) * Real.cos (2 * Real.pi * p 1)) * v 0 -
            ((2 : ℝ) + Real.cos (2 * Real.pi * p 0)) * (2 * Real.pi) *
              Real.sin (2 * Real.pi * p 1) * v 1,
          -((2 * Real.pi) * Real.sin (2 * Real.pi * p 0) * Real.sin (2 * Real.pi * p 1)) * v 0 +
            ((2 : ℝ) + Real.cos (2 * Real.pi * p 0)) * (2 * Real.pi) *
              Real.cos (2 * Real.pi * p 1) * v 1,
          (2 * Real.pi) * Real.cos (2 * Real.pi * p 0) * v 0
        ] := by
    ext i
    fin_cases i
    · simp [L0, PiLp.proj_apply, smul_eq_mul]; try ring
    · simp [L1, PiLp.proj_apply, smul_eq_mul]; try ring
    · simp [L2, PiLp.proj_apply, smul_eq_mul]; try ring
  convert congrArg (WithLp.toLp 2) htuple using 1
  ext i
  fin_cases i <;> rfl

/-- Helper for Example 4.2: the derivative of the torus parameterization is injective at every
point. -/
theorem torus_revolution_map_fderiv_injective (p : EuclideanSpace ℝ (Fin 2)) :
    Function.Injective (fderiv ℝ torus_revolution_map p) := by
  intro v w hvw
  let wπ : ℝ := 2 * Real.pi
  have hω : wπ ≠ 0 := ne_of_gt (by positivity)
  have hdiff :
      fderiv ℝ torus_revolution_map p (v - w) = 0 := by
    simp [map_sub, hvw]
  have hx := congrArg (fun y : EuclideanSpace ℝ (Fin 3) ↦ y 0) hdiff
  have hy := congrArg (fun y : EuclideanSpace ℝ (Fin 3) ↦ y 1) hdiff
  have hz := congrArg (fun y : EuclideanSpace ℝ (Fin 3) ↦ y 2) hdiff
  have hx' :
      - (wπ * Real.sin (wπ * p 0) * Real.cos (wπ * p 1)) * (v 0 - w 0) -
          ((2 : ℝ) + Real.cos (wπ * p 0)) * wπ * Real.sin (wπ * p 1) * (v 1 - w 1) = 0 := by
    simpa [torus_revolution_map_fderiv_apply, wπ] using hx
  have hy' :
      - (wπ * Real.sin (wπ * p 0) * Real.sin (wπ * p 1)) * (v 0 - w 0) +
          ((2 : ℝ) + Real.cos (wπ * p 0)) * wπ * Real.cos (wπ * p 1) * (v 1 - w 1) = 0 := by
    simpa [torus_revolution_map_fderiv_apply, wπ] using hy
  have hz' :
      wπ * Real.cos (wπ * p 0) * (v 0 - w 0) = 0 := by
    simpa [torus_revolution_map_fderiv_apply, wπ] using hz
  have hcos_delta0 : Real.cos (wπ * p 0) * (v 0 - w 0) = 0 := by
    have hz'' : wπ * (Real.cos (wπ * p 0) * (v 0 - w 0)) = 0 := by
      convert hz' using 1
      ring
    exact (mul_eq_zero.mp hz'').resolve_left hω
  have hsin_delta0 : Real.sin (wπ * p 0) * (v 0 - w 0) = 0 := by
    have hx'' := congrArg (fun t : ℝ ↦ Real.cos (wπ * p 1) * t) hx'
    have hy'' := congrArg (fun t : ℝ ↦ Real.sin (wπ * p 1) * t) hy'
    have hcomb :
        Real.cos (wπ * p 1) *
            (- (wπ * Real.sin (wπ * p 0) * Real.cos (wπ * p 1)) * (v 0 - w 0) -
              ((2 : ℝ) + Real.cos (wπ * p 0)) * wπ * Real.sin (wπ * p 1) * (v 1 - w 1)) +
          Real.sin (wπ * p 1) *
            (- (wπ * Real.sin (wπ * p 0) * Real.sin (wπ * p 1)) * (v 0 - w 0) +
              ((2 : ℝ) + Real.cos (wπ * p 0)) * wπ * Real.cos (wπ * p 1) * (v 1 - w 1)) = 0 := by
      linarith
    ring_nf at hcomb
    have : -wπ * Real.sin (wπ * p 0) * (v 0 - w 0) = 0 := by
      nlinarith [hcomb, Real.sin_sq_add_cos_sq (wπ * p 1)]
    have hωsin : wπ * (Real.sin (wπ * p 0) * (v 0 - w 0)) = 0 := by
      linarith
    exact (mul_eq_zero.mp hωsin).resolve_left hω
  have hdelta0 : v 0 - w 0 = 0 := by
    have hsq : (v 0 - w 0) ^ 2 = 0 := by
      nlinarith [Real.sin_sq_add_cos_sq (wπ * p 0), hsin_delta0, hcos_delta0]
    nlinarith
  have hA : 0 < (2 : ℝ) + Real.cos (wπ * p 0) := torus_revolution_factor_cos_pos (wπ * p 0)
  have hsin_delta1 : Real.sin (wπ * p 1) * (v 1 - w 1) = 0 := by
    have hx0 : -((2 : ℝ) + Real.cos (wπ * p 0)) * wπ * Real.sin (wπ * p 1) * (v 1 - w 1) = 0 := by
      rw [hdelta0] at hx'
      linarith
    have hωA : ((2 : ℝ) + Real.cos (wπ * p 0)) * wπ ≠ 0 :=
      mul_ne_zero (ne_of_gt hA) hω
    have : ((2 : ℝ) + Real.cos (wπ * p 0)) * wπ * (Real.sin (wπ * p 1) * (v 1 - w 1)) = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left hωA
  have hcos_delta1 : Real.cos (wπ * p 1) * (v 1 - w 1) = 0 := by
    have hy0 : ((2 : ℝ) + Real.cos (wπ * p 0)) * wπ * Real.cos (wπ * p 1) * (v 1 - w 1) = 0 := by
      rw [hdelta0] at hy'
      linarith
    have hωA : ((2 : ℝ) + Real.cos (wπ * p 0)) * wπ ≠ 0 :=
      mul_ne_zero (ne_of_gt hA) hω
    have : ((2 : ℝ) + Real.cos (wπ * p 0)) * wπ * (Real.cos (wπ * p 1) * (v 1 - w 1)) = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left hωA
  have hdelta1 : v 1 - w 1 = 0 := by
    have hsq : (v 1 - w 1) ^ 2 = 0 := by
      nlinarith [Real.sin_sq_add_cos_sq (wπ * p 1), hsin_delta1, hcos_delta1]
    nlinarith
  ext i
  fin_cases i
  · exact sub_eq_zero.mp hdelta0
  · exact sub_eq_zero.mp hdelta1

/-- Example 4.2 (5): the explicit torus parameterization is a smooth immersion
`ℝ^2 → ℝ^3`. -/
theorem torus_revolution_map_isImmersion :
    Manifold.IsImmersion (𝓡 2) (𝓡 3) ∞ torus_revolution_map := by
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv
    torus_revolution_map_contMDiff).2 ?_
  intro p
  rw [mfderiv_eq_fderiv]
  exact torus_revolution_map_fderiv_injective p

/-- Helper for Example 4.2: the image of the torus parameterization lies on the torus of
revolution. -/
lemma torus_revolution_map_mem_surface (p : EuclideanSpace ℝ (Fin 2)) :
    torus_revolution_map p ∈ torus_revolution_surface := by
  set u := p 0
  set v := p 1
  set r := (2 : ℝ) + Real.cos (2 * Real.pi * u)
  have hrpos : 0 < r := torus_revolution_factor_cos_pos (2 * Real.pi * u)
  have hxy :
      (torus_revolution_map p 0) ^ 2 + (torus_revolution_map p 1) ^ 2 = r ^ 2 := by
    simp [torus_revolution_map, r, u, mul_pow]
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * v)]
  have hsqrt : Real.sqrt ((torus_revolution_map p 0) ^ 2 + (torus_revolution_map p 1) ^ 2) = r := by
    rw [hxy, Real.sqrt_sq (le_of_lt hrpos)]
  change
    (Real.sqrt ((torus_revolution_map p 0) ^ 2 + (torus_revolution_map p 1) ^ 2) - 2) ^ 2 +
        (torus_revolution_map p 2) ^ 2 = 1
  rw [hsqrt]
  have hz : torus_revolution_map p 2 = Real.sin (2 * Real.pi * u) := by
    simp [torus_revolution_map, u]
  have hr2 : r - 2 = Real.cos (2 * Real.pi * u) := by simp [r]
  rw [hz, hr2, add_comm]
  exact Real.sin_sq_add_cos_sq (2 * Real.pi * u)

/-- Helper for Example 4.2: a point of the torus of revolution is hit by the parameterization. -/
lemma mem_range_torus_revolution_map_of_mem_surface {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ torus_revolution_surface) :
    x ∈ Set.range torus_revolution_map := by
  have hxeq :
      (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - 2) ^ 2 + x 2 ^ 2 = 1 :=
    (mem_torus_revolution_surface_iff).1 hx
  set ρ := Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
  have hρsq : ρ ^ 2 = x 0 ^ 2 + x 1 ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hρ_mem : |ρ - 2| ≤ 1 := by
    have : (ρ - 2) ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith [sq_nonneg (x 2), hxeq]
    exact abs_le_of_sq_le_sq this (by positivity)
  have hρ_ge : (1 : ℝ) ≤ ρ := by
    have := abs_le.mp hρ_mem
    linarith
  have hρ_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ_ge
  let zθ : ℂ := ⟨ρ - 2, x 2⟩
  have hθnorm : ‖zθ‖ = 1 :=
    complex_norm_eq_one_of_re_sq_add_im_sq (by simpa [zθ, ρ] using hxeq)
  let θ : ℝ := zθ.arg
  have hcosθ : Real.cos θ = ρ - 2 := by
    have := Complex.norm_mul_cos_arg zθ
    simpa [hθnorm, θ, zθ] using this
  have hsinθ : Real.sin θ = x 2 := by
    have := Complex.norm_mul_sin_arg zθ
    simpa [hθnorm, θ, zθ] using this
  let zφ : ℂ := ⟨x 0 / ρ, x 1 / ρ⟩
  have hφsq : (x 0 / ρ) ^ 2 + (x 1 / ρ) ^ 2 = 1 := by
    field_simp [hρ_pos.ne']
    nlinarith [hρsq]
  have hφnorm : ‖zφ‖ = 1 := complex_norm_eq_one_of_re_sq_add_im_sq hφsq
  let φ : ℝ := zφ.arg
  have hcosφ : Real.cos φ = x 0 / ρ := by
    have := Complex.norm_mul_cos_arg zφ
    simpa [hφnorm, φ, zφ] using this
  have hsinφ : Real.sin φ = x 1 / ρ := by
    have := Complex.norm_mul_sin_arg zφ
    simpa [hφnorm, φ, zφ] using this
  have hω : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
  let p : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 ![θ / (2 * Real.pi), φ / (2 * Real.pi)]
  refine ⟨p, ?_⟩
  have hp0 : p 0 = θ / (2 * Real.pi) := by simp [p]
  have hp1 : p 1 = φ / (2 * Real.pi) := by simp [p]
  have hωθ : 2 * Real.pi * p 0 = θ := by
    simp [hp0, mul_div_cancel₀ _ hω]
  have hωφ : 2 * Real.pi * p 1 = φ := by
    simp [hp1, mul_div_cancel₀ _ hω]
  have hr : (2 : ℝ) + Real.cos (2 * Real.pi * p 0) = ρ := by
    simp [hωθ, hcosθ]
  ext i
  fin_cases i
  · have : torus_revolution_map p 0 = ρ * Real.cos φ := by
      simp [torus_revolution_map, hr, hωφ]
    simpa [this, hcosφ] using mul_div_cancel₀ (x 0) hρ_pos.ne'
  · have : torus_revolution_map p 1 = ρ * Real.sin φ := by
      simp [torus_revolution_map, hr, hωφ]
    simpa [this, hsinφ] using mul_div_cancel₀ (x 1) hρ_pos.ne'
  · simp [torus_revolution_map, hωθ, hsinθ]

/-- Example 4.2 (6): the image of the torus parameterization is the torus of revolution obtained by
rotating the circle `(y - 2)^2 + z^2 = 1` about the `z`-axis. -/
theorem range_torus_revolution_map :
    Set.range torus_revolution_map = torus_revolution_surface := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact torus_revolution_map_mem_surface p
  · exact mem_range_torus_revolution_map_of_mem_surface
