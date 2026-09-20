import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import LeeSmoothLib.Ch03.Sec03_13.Definition_3_13_extra_1
import LeeSmoothLib.Ch03.Sec03_13.Definition_3_13_extra_3
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory Set
open scoped ContDiff Interval Manifold

-- Semantic search note: the `lean_leansearch` MCP tool was unavailable in this session, so this
-- file uses local repository precedent plus mathlib inspection of `PointDerivation`,
-- `Derivation.mk'`, and `EuclideanSpace.projₗ`.

variable {n : ℕ}

local notation "R^n" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "SmoothRn" => C^∞⟮I, EuclideanSpace ℝ (Fin n); ℝ⟯

namespace Proposition3_2_Hadamard

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
variable [FiniteDimensional ℝ E]

/-- The derivative of a function on a product, restricted to the first factor. -/
noncomputable def partialFDeriv (F : E × ℝ → G) (p : E × ℝ) : E →L[ℝ] G :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)

omit [CompleteSpace G] [FiniteDimensional ℝ E] in
theorem partialFDeriv_continuous {F : E × ℝ → G} (hF : ContDiff ℝ 1 F) :
    Continuous (partialFDeriv F) := by
  unfold partialFDeriv
  fun_prop

omit [CompleteSpace G] [FiniteDimensional ℝ E] in
theorem partialFDeriv_hasFDerivAt {F : E × ℝ → G} (hF : ContDiff ℝ 1 F)
    (x : E) (t : ℝ) :
    HasFDerivAt (fun y ↦ F (y, t)) (partialFDeriv F (x, t)) x := by
  have hfull : HasFDerivAt F (fderiv ℝ F (x, t)) (x, t) :=
    (hF.differentiable (by simp) (x, t)).hasFDerivAt
  have hpair : HasFDerivAt (fun y : E ↦ (y, t))
      (ContinuousLinearMap.inl ℝ E ℝ) x := by
    fun_prop
  change HasFDerivAt (F ∘ fun y : E ↦ (y, t))
    ((fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x
  exact hfull.comp x hpair

omit [CompleteSpace G] in
theorem hasFDerivAt_intervalIntegral_of_contDiff {F : E × ℝ → G}
    (hF : ContDiff ℝ 1 F) (x : E) :
    HasFDerivAt (fun y ↦ ∫ t in (0 : ℝ)..1, F (y, t))
      (∫ t in (0 : ℝ)..1, partialFDeriv F (x, t)) x := by
  let K : Set (E × ℝ) := Metric.closedBall x 1 ×ˢ Icc 0 1
  have hK : IsCompact K := (isCompact_closedBall x 1).prod isCompact_Icc
  have hpartial : Continuous (partialFDeriv F) := partialFDeriv_continuous hF
  have hbdd : Bornology.IsBounded (partialFDeriv F '' K) :=
    (hK.image hpartial).isBounded
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : E →L[ℝ] G)).mp hbdd
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (μ := MeasureTheory.volume) (F := fun y t ↦ F (y, t))
    (F' := fun y t ↦ partialFDeriv F (y, t))
    (x₀ := x) (a := 0) (b := 1) (s := Metric.ball x 1) (bound := fun _ ↦ C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Metric.ball_mem_nhds x zero_lt_one
  · filter_upwards [] with y
    exact (hF.continuous.comp (.prodMk_right y)).aestronglyMeasurable.restrict
  · exact (hF.continuous.comp (.prodMk_right x)).intervalIntegrable
      (μ := MeasureTheory.volume) 0 1
  · exact (hpartial.comp (.prodMk_right x)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro y hy
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht
    have hxy : (y, t) ∈ K := ⟨Metric.mem_closedBall.mpr hy.le, ht'⟩
    have himage : partialFDeriv F (y, t) ∈ partialFDeriv F '' K :=
      ⟨(y, t), hxy, rfl⟩
    have hball := hC himage
    simpa [Metric.mem_closedBall, dist_zero_right] using hball
  · exact intervalIntegrable_const
  · filter_upwards with t
    intro y hy
    exact partialFDeriv_hasFDerivAt hF y t

omit [CompleteSpace G] [FiniteDimensional ℝ E] in
theorem partialFDeriv_contDiff {F : E × ℝ → G} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (partialFDeriv F) := by
  have hfder : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  unfold partialFDeriv
  fun_prop

theorem intervalIntegral_contDiff_nat (m : ℕ) {F : E × ℝ → G}
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ m (fun x ↦ ∫ t in (0 : ℝ)..1, F (x, t)) := by
  induction m generalizing G with
  | zero =>
      change ContDiff ℝ (0 : ℕ∞ω) (fun x ↦ ∫ t in (0 : ℝ)..1, F (x, t))
      exact contDiff_zero.mpr <| continuous_iff_continuousAt.mpr fun x ↦
        (hasFDerivAt_intervalIntegral_of_contDiff (hF.of_le (by simp)) x).continuousAt
  | succ m ih =>
      rw [show (m + 1 : ℕ) = (m : ℕ∞ω) + 1 by norm_num]
      rw [contDiff_succ_iff_fderiv]
      refine ⟨fun x ↦ (hasFDerivAt_intervalIntegral_of_contDiff
        (hF.of_le (by simp)) x).differentiableAt, by simp, ?_⟩
      have hpartial : ContDiff ℝ ∞ (partialFDeriv F) := partialFDeriv_contDiff hF
      have hi := ih hpartial
      convert hi using 1
      funext x
      exact (hasFDerivAt_intervalIntegral_of_contDiff (hF.of_le (by simp)) x).fderiv

theorem intervalIntegral_contDiff {F : E × ℝ → G} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x ↦ ∫ t in (0 : ℝ)..1, F (x, t)) := by
  rw [contDiff_infty]
  intro m
  exact intervalIntegral_contDiff_nat m hF

noncomputable def hadamardFactor (a : R^n) (f : R^n → ℝ) (i : Fin n)
    (x : R^n) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    fderiv ℝ f (a + t • (x - a)) (EuclideanSpace.basisFun (Fin n) ℝ i)

theorem hadamardFactor_contDiff (a : R^n) {f : R^n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    ContDiff ℝ ∞ (hadamardFactor a f i) := by
  unfold hadamardFactor
  let F : R^n × ℝ → ℝ := fun p ↦
    fderiv ℝ f (a + p.2 • (p.1 - a)) (EuclideanSpace.basisFun (Fin n) ℝ i)
  change ContDiff ℝ ∞ (fun x ↦ ∫ t in (0 : ℝ)..1, F (x, t))
  apply intervalIntegral_contDiff
  have hfder : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  dsimp only [F]
  fun_prop

theorem euclidean_eq_sum_coordinates (x : R^n) :
    x = ∑ i, x i • EuclideanSpace.basisFun (Fin n) ℝ i := by
  classical
  apply PiLp.ext
  intro j
  simp [EuclideanSpace.basisFun_apply, Pi.single_apply]

theorem hadamard_decomposition (a : R^n) {f : R^n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : R^n) :
    f x = f a + ∑ i, (x i - a i) * hadamardFactor a f i x := by
  classical
  have htaylor₀ := map_add_eq_sum_add_integral_iteratedFDeriv
    (n := 0) (f := f) (x := a) (y := x - a)
    (fun t _ ↦ hf.contDiffAt.of_le (by simp))
  have htaylor : f x = f a + ∫ t in (0 : ℝ)..1,
      fderiv ℝ f (a + t • (x - a)) (x - a) := by
    simpa only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.factorial_zero,
      Nat.cast_one, inv_one, iteratedFDeriv_zero_apply, one_smul, pow_zero,
      Nat.reduceAdd, iteratedFDeriv_one_apply, show a + (x - a) = x by abel] using htaylor₀
  have hvec : x - a =
      ∑ i, (x i - a i) • EuclideanSpace.basisFun (Fin n) ℝ i := by
    rw [euclidean_eq_sum_coordinates (x - a)]
    simp only [PiLp.sub_apply]
  rw [htaylor]
  congr 1
  rw [intervalIntegral.integral_congr (g := fun t ↦ ∑ i,
    (x i - a i) * fderiv ℝ f (a + t • (x - a))
      (EuclideanSpace.basisFun (Fin n) ℝ i))]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, hadamardFactor]
  · intro i _
    apply Continuous.intervalIntegrable
    have hfderSmooth : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hfder : Continuous (fderiv ℝ f) := hfderSmooth.continuous
    fun_prop
  · intro t _
    simp only [hvec, map_sum, map_smul, smul_eq_mul]

noncomputable def hadamardFactorMap (a : R^n) (f : SmoothRn) (i : Fin n) :
    SmoothRn :=
  ⟨hadamardFactor a f i,
    (hadamardFactor_contDiff a f.contMDiff.contDiff i).contMDiff⟩

theorem hadamardFactorMap_apply_base (a : R^n) (f : SmoothRn) (i : Fin n) :
    hadamardFactorMap a f i a =
      fderiv ℝ f a (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  simp [hadamardFactorMap, hadamardFactor]

end Proposition3_2_Hadamard

/-- The `i`-th coordinate function on `ℝ^n`, viewed as a smooth real-valued map. -/
def coordinate_cont_mdiff_map (i : Fin n) : SmoothRn :=
  (EuclideanSpace.proj i : R^n →L[ℝ] ℝ)

/-- Applying the smooth coordinate projection returns the corresponding coordinate. -/
theorem coordinate_cont_mdiff_map_apply (i : Fin n) (x : R^n) :
    coordinate_cont_mdiff_map i x = x i := by
  rfl

namespace Proposition3_2_Hadamard

theorem smooth_hadamard_decomposition (a : R^n) (f : SmoothRn) :
    f = ContMDiffMap.const (f a) + ∑ i,
      (coordinate_cont_mdiff_map i - ContMDiffMap.const (a i)) *
        hadamardFactorMap a f i := by
  ext x
  let evx : SmoothRn →+ ℝ :=
    { toFun := fun g ↦ g x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change evx f = evx (ContMDiffMap.const (f a) + ∑ i,
    (coordinate_cont_mdiff_map i - ContMDiffMap.const (a i)) *
      hadamardFactorMap a f i)
  rw [map_add, map_sum]
  change f x = f a + ∑ i, (x i - a i) * hadamardFactor a f i x
  exact hadamard_decomposition a f.contMDiff.contDiff x

theorem point_derivation_eq_coordinate_sum (a : R^n) (w : PointDerivation I a)
    (f : SmoothRn) :
    w f = ∑ i, w (coordinate_cont_mdiff_map i) *
      fderiv ℝ f a (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hconst (c : ℝ) : w (ContMDiffMap.const c) = 0 := by
    exact w.map_algebraMap c
  calc
    w f = w (ContMDiffMap.const (f a) + ∑ i,
        (coordinate_cont_mdiff_map i - ContMDiffMap.const (a i)) *
          hadamardFactorMap a f i) :=
      congrArg (fun g : SmoothRn ↦ w g) (smooth_hadamard_decomposition a f)
    _ = ∑ i, w (coordinate_cont_mdiff_map i) * hadamardFactorMap a f i a := by
      rw [map_add, map_sum, hconst, zero_add]
      apply Finset.sum_congr rfl
      intro i _
      rw [w.leibniz]
      simp only [PointedContMDiffMap.smul_def]
      have hcoord :
          (coordinate_cont_mdiff_map i -
            (ContMDiffMap.const (a i) : SmoothRn)) a = 0 := by
        change a i - a i = 0
        exact sub_self _
      rw [hcoord, zero_mul, zero_add, map_sub, hconst, sub_zero]
      exact mul_comm _ _
    _ = ∑ i, w (coordinate_cont_mdiff_map i) *
        fderiv ℝ f a (EuclideanSpace.basisFun (Fin n) ℝ i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hadamardFactorMap_apply_base]

end Proposition3_2_Hadamard

/-- The directional derivative at `a` is additive in the smooth function argument. -/
theorem directional_fderiv_map_add (a : R^n) (v : geometric_tangent_space a)
    (f g : SmoothRn) :
    fderiv ℝ (f + g) a v = fderiv ℝ f a v + fderiv ℝ g a v := by
  have hf : DifferentiableAt ℝ (f : R^n → ℝ) a :=
    (f.contMDiff.contDiff.differentiable (by simp)) a
  have hg : DifferentiableAt ℝ (g : R^n → ℝ) a :=
    (g.contMDiff.contDiff.differentiable (by simp)) a
  exact congrArg (fun L : R^n →L[ℝ] ℝ ↦ L v) (fderiv_add hf hg)

/-- The directional derivative at `a` is `ℝ`-linear in the smooth function argument. -/
theorem directional_fderiv_map_smul (a : R^n) (v : geometric_tangent_space a)
    (c : ℝ) (f : SmoothRn) :
    fderiv ℝ (c • f) a v = c * fderiv ℝ f a v := by
  have hf : DifferentiableAt ℝ (f : R^n → ℝ) a :=
    (f.contMDiff.contDiff.differentiable (by simp)) a
  simpa [smul_eq_mul] using
    congrArg (fun L : R^n →L[ℝ] ℝ ↦ L v) (fderiv_const_smul hf c)

/-- The directional derivative at `a` satisfies the Leibniz rule on smooth real-valued functions
on `ℝ^n`. -/
theorem directional_fderiv_leibniz_formula (a : R^n) (v : geometric_tangent_space a)
    (f g : SmoothRn) :
    fderiv ℝ (f * g) a v = f a * fderiv ℝ g a v + g a * fderiv ℝ f a v := by
  have hf : DifferentiableAt ℝ (f : R^n → ℝ) a :=
    (f.contMDiff.contDiff.differentiable (by simp)) a
  have hg : DifferentiableAt ℝ (g : R^n → ℝ) a :=
    (g.contMDiff.contDiff.differentiable (by simp)) a
  simpa [smul_eq_mul] using
    congrArg (fun L : R^n →L[ℝ] ℝ ↦ L v) (fderiv_mul hf hg)

/-- The directional derivative at `a` along the based vector `v` packaged as a point derivation. -/
def directional_point_derivation (a : R^n) (v : geometric_tangent_space a) :
    PointDerivation I a :=
  Derivation.mk'
    { toFun := fun f ↦ fderiv ℝ f a v
      map_add' := fun f g ↦ directional_fderiv_map_add a v f g
      map_smul' := fun c f ↦ directional_fderiv_map_smul a v c f }
    (fun f g ↦ directional_fderiv_leibniz_formula a v f g)

/-- Evaluating `directional_point_derivation` is evaluation of the Fréchet derivative in the
direction `v`. -/
theorem directional_point_derivation_apply (a : R^n) (v : geometric_tangent_space a)
    (f : SmoothRn) :
    directional_point_derivation a v f = fderiv ℝ f a v := by
  rfl

/-- Proposition 3.2 (1): for each geometric tangent vector `v ∈ ℝ_a^n`, the associated map
`Dᵥ|ₐ` is a derivation at `a` on smooth real-valued functions on `ℝ^n`. -/
theorem directional_point_derivation_leibniz (a : R^n) (v : geometric_tangent_space a)
    (f g : SmoothRn) :
    directional_point_derivation a v (f * g) =
      f a * directional_point_derivation a v g +
        g a * directional_point_derivation a v f := by
  simpa only [directional_point_derivation_apply] using
    directional_fderiv_leibniz_formula a v f g

/-- The assignment `v ↦ Dᵥ|ₐ` is additive in the geometric tangent vector. -/
theorem geometric_to_point_derivation_map_add (a : R^n)
    (v w : geometric_tangent_space a) :
    directional_point_derivation a (v + w) =
      directional_point_derivation a v +
        directional_point_derivation a w := by
  ext f
  change fderiv ℝ f a (v + w) = fderiv ℝ f a v + fderiv ℝ f a w
  exact (fderiv ℝ f a).map_add v w

/-- The assignment `v ↦ Dᵥ|ₐ` is `ℝ`-linear in the geometric tangent vector. -/
theorem geometric_to_point_derivation_map_smul (a : R^n) (c : ℝ)
    (v : geometric_tangent_space a) :
    directional_point_derivation a (c • v) =
      c • directional_point_derivation a v := by
  ext f
  change fderiv ℝ f a (c • v) = c • fderiv ℝ f a v
  exact (fderiv ℝ f a).map_smul c v

/-- The map sending a geometric tangent vector at `a` to its associated point derivation. -/
def geometric_to_point_derivation (a : R^n) :
    geometric_tangent_space a →ₗ[ℝ] PointDerivation I a where
  toFun := directional_point_derivation a
  map_add' := fun v w ↦ geometric_to_point_derivation_map_add a v w
  map_smul' := fun c v ↦ geometric_to_point_derivation_map_smul a c v

/-- Applying `geometric_to_point_derivation` sends `v` to the directional point derivation
`Dᵥ|ₐ`. -/
theorem geometric_to_point_derivation_apply (a : R^n) (v : geometric_tangent_space a) :
    geometric_to_point_derivation a v =
      directional_point_derivation a v := by
  rfl

/-- The coordinate-evaluation recipe recovers a geometric tangent vector from a point derivation. -/
theorem point_derivation_to_geometric_map_add_formula (a : R^n)
    (w₁ w₂ : PointDerivation I a) :
    (∑ i, (w₁ + w₂) (coordinate_cont_mdiff_map i) •
        EuclideanSpace.basisFun (Fin n) ℝ i) =
      (∑ i, w₁ (coordinate_cont_mdiff_map i) • EuclideanSpace.basisFun (Fin n) ℝ i) +
        ∑ i,
          w₂ (coordinate_cont_mdiff_map i) • EuclideanSpace.basisFun (Fin n) ℝ i := by
  simp only [Derivation.add_apply, add_smul, Finset.sum_add_distrib]

/-- The coordinate-evaluation recipe is `ℝ`-linear in the point derivation. -/
theorem point_derivation_to_geometric_map_smul_formula (a : R^n) (c : ℝ)
    (w : PointDerivation I a) :
    (∑ i, (c • w) (coordinate_cont_mdiff_map i) •
        EuclideanSpace.basisFun (Fin n) ℝ i) =
      c • ∑ i,
        w (coordinate_cont_mdiff_map i) • EuclideanSpace.basisFun (Fin n) ℝ i := by
  simp only [Derivation.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

/-- Recover a geometric tangent vector from a point derivation by evaluating it on the coordinate
functions. -/
def point_derivation_to_geometric (a : R^n) :
    PointDerivation I a →ₗ[ℝ] geometric_tangent_space a where
  toFun := fun w ↦
    ∑ i, w (coordinate_cont_mdiff_map i) • EuclideanSpace.basisFun (Fin n) ℝ i
  map_add' := fun w₁ w₂ ↦ point_derivation_to_geometric_map_add_formula a w₁ w₂
  map_smul' := fun c w ↦ point_derivation_to_geometric_map_smul_formula a c w

/-- Projecting `point_derivation_to_geometric` to coordinate `i` recovers the derivation applied
to the `i`-th coordinate function. -/
theorem point_derivation_to_geometric_proj (a : R^n) (w : PointDerivation I a) (i : Fin n) :
    EuclideanSpace.proj i (point_derivation_to_geometric a w) =
      w (coordinate_cont_mdiff_map i) := by
  classical
  change (∑ j, w (coordinate_cont_mdiff_map j) •
    EuclideanSpace.basisFun (Fin n) ℝ j) i = w (coordinate_cont_mdiff_map i)
  simp [EuclideanSpace.basisFun_apply, Pi.single_apply]

/-- Applying `point_derivation_to_geometric` after `directional_point_derivation` recovers the
original geometric tangent vector. -/
theorem geometric_to_point_derivation_left_inv (a : R^n) (v : geometric_tangent_space a) :
    point_derivation_to_geometric a (directional_point_derivation a v) = v := by
  apply PiLp.ext
  intro i
  change EuclideanSpace.proj i
      (point_derivation_to_geometric a (directional_point_derivation a v)) =
    EuclideanSpace.proj i v
  rw [point_derivation_to_geometric_proj, directional_point_derivation_apply]
  change fderiv ℝ (EuclideanSpace.proj i) a v = EuclideanSpace.proj i v
  rw [ContinuousLinearMap.fderiv]

/-- Applying `directional_point_derivation` after `point_derivation_to_geometric` recovers the
original point derivation. -/
theorem geometric_to_point_derivation_right_inv (a : R^n) (w : PointDerivation I a) :
    directional_point_derivation a (point_derivation_to_geometric a w) = w := by
  ext f
  rw [directional_point_derivation_apply]
  change fderiv ℝ f a
    (∑ i, w (coordinate_cont_mdiff_map i) • EuclideanSpace.basisFun (Fin n) ℝ i) = w f
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  exact (Proposition3_2_Hadamard.point_derivation_eq_coordinate_sum a w f).symm

/-- Proposition 3.2 (2): the map `v ↦ Dᵥ|ₐ` is a linear isomorphism from the geometric tangent
space `ℝ_a^n` onto the point-derivation tangent space `T_aℝ^n`. -/
def geometric_to_point_derivation_linear_equiv (a : R^n) :
    geometric_tangent_space a ≃ₗ[ℝ] PointDerivation I a where
  toLinearMap := geometric_to_point_derivation a
  invFun := point_derivation_to_geometric a
  left_inv := geometric_to_point_derivation_left_inv a
  right_inv := geometric_to_point_derivation_right_inv a

/-- The forward direction of `geometric_to_point_derivation_linear_equiv` is the map
`v ↦ Dᵥ|ₐ`. -/
theorem geometric_to_point_derivation_linear_equiv_apply (a : R^n)
    (v : geometric_tangent_space a) :
    geometric_to_point_derivation_linear_equiv a v =
      directional_point_derivation a v := by
  rfl
