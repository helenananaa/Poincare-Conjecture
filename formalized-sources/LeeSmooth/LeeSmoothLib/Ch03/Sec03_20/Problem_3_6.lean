import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.ProdL2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

-- Local API note: semantic `lean_leansearch` was unavailable in this session; mathlib's sphere
-- manifold instance for the Euclidean `ℂ²` model uses the `L²` product type `WithLp 2 (ℂ × ℂ)`.
local notation "C2" => WithLp 2 (ℂ × ℂ)
local notation "unitSphere3" => Metric.sphere (0 : C2) 1

-- Keep all structures on the `L²` product definitionally aligned.  Both the generic `WithLp`
-- module instances and the real inner-product-space instances are available here; fixing the
-- inherited structures avoids a typeclass diamond when comparing `fderiv` and `mfderiv`.
private abbrev problem36C2NAG : NormedAddCommGroup C2 :=
  WithLp.instProdNormedAddCommGroup 2 ℂ ℂ

private abbrev problem36C2NS : NormedSpace ℝ C2 :=
  WithLp.instProdInnerProductSpace.toNormedSpace

private abbrev problem36C2AG : AddCommGroup C2 :=
  @NormedAddCommGroup.toAddCommGroup C2 problem36C2NAG

private abbrev problem36C2Module : Module ℝ C2 :=
  @NormedSpace.toModule ℝ C2 inferInstance
    (@NormedAddCommGroup.toSeminormedAddCommGroup C2 problem36C2NAG) problem36C2NS

private abbrev problem36C2Topology : TopologicalSpace C2 :=
  @UniformSpace.toTopologicalSpace C2
    (@PseudoMetricSpace.toUniformSpace C2
      (@MetricSpace.toPseudoMetricSpace C2
        (@NormedAddCommGroup.toMetricSpace C2 problem36C2NAG)))

attribute [local instance]
  problem36C2NS problem36C2AG problem36C2Module problem36C2Topology

-- Proof sketch: identify `ℂ` with `ℝ²`, use additivity of `finrank` on products, and simplify.
/-- The real vector space underlying `ℂ²` has dimension `4`. -/
theorem finrank_real_complex_pair : Module.finrank ℝ C2 = 3 + 1 := by
  calc
    Module.finrank ℝ C2 = Module.finrank ℝ (ℂ × ℂ) :=
      (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).finrank_eq
    _ = 3 + 1 := by simp [Module.finrank_prod, Complex.finrank_real_complex]

/-- The standard sphere in `ℂ²` uses the real-dimension-four sphere manifold structure. -/
local instance complex_pair_finrank_fact : Fact (Module.finrank ℝ C2 = 3 + 1) :=
  ⟨finrank_real_complex_pair⟩

-- Proof sketch: `|exp (tI)| = 1`, so multiplying each complex coordinate by `exp (tI)` preserves
-- the sum of squared norms that defines the unit sphere in `ℂ²`.
/-- Rotating both complex coordinates of a point of `S³ ⊆ ℂ²` by the same phase keeps the point on
the sphere. -/
theorem sphere3_phase_curve_mem (z : unitSphere3) (t : ℝ) :
    WithLp.toLp 2
        (Complex.exp (t * Complex.I) * (z : C2).fst,
          Complex.exp (t * Complex.I) * (z : C2).snd) ∈
      unitSphere3 := by
  rw [mem_sphere_zero_iff_norm]
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I]
  have hz : ‖(z : C2)‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
  have hzsq := congrArg (fun x : ℝ ↦ x ^ 2) hz
  rw [WithLp.prod_norm_sq_eq_of_L2] at hzsq
  norm_num at hzsq ⊢
  exact hzsq

/-- The phase-rotation curve on `S³` through `z`, obtained by multiplying both complex coordinates
by `exp (it)`. -/
def sphere3_phase_curve (z : unitSphere3) : ℝ → unitSphere3 :=
  fun t ↦ ⟨WithLp.toLp 2
      (Complex.exp (t * Complex.I) * (z : C2).fst,
        Complex.exp (t * Complex.I) * (z : C2).snd),
    sphere3_phase_curve_mem z t⟩

-- Proof sketch: unfold `sphere3_phase_curve`; the underlying ambient point is the ordered pair
-- used in its definition.
/-- The ambient-value formula for the phase-rotation curve on `S³`. -/
theorem sphere3_phase_curve_coe (z : unitSphere3) (t : ℝ) :
    ((sphere3_phase_curve z t : unitSphere3) : C2) =
      WithLp.toLp 2
        (Complex.exp (t * Complex.I) * (z : C2).fst,
          Complex.exp (t * Complex.I) * (z : C2).snd) := rfl

-- Proof sketch: first view the curve as the codomain restriction of the smooth ambient map
-- `t ↦ exp (tI) • z`; smoothness follows from smoothness of `Complex.exp` and multiplication.
-- For the velocity, compute the derivative in `ℂ²`, note that it equals multiplication by
-- `I * exp (tI)`, and use injectivity of the sphere inclusion differential together with `z ≠ 0`.
set_option backward.isDefEq.respectTransparency true in
/-- Problem 3-6: for each `z ∈ S³ ⊆ ℂ²`, the curve `t ↦ (e^{it} z¹, e^{it} z²)` is smooth and its
velocity is nonzero at every parameter value. -/
theorem sphere3_phase_curve_smooth_and_velocity_ne_zero (z : unitSphere3) :
    ContMDiff 𝓘(ℝ) (𝓡 3) ∞ (sphere3_phase_curve z) ∧
      ∀ t : ℝ,
        mfderiv (𝓘(ℝ)) (𝓡 3) (sphere3_phase_curve z) t
          (show TangentSpace 𝓘(ℝ) t from (1 : ℝ)) ≠ 0 := by
  have hphaseScalar : ContDiff ℝ ∞ (fun t : ℝ ↦ Complex.exp (t * Complex.I)) := by
    apply ContDiff.cexp
    exact Complex.ofRealCLM.contDiff.mul contDiff_const
  have hfirst : ContDiff ℝ ∞
      (fun t : ℝ ↦ Complex.exp (t * Complex.I) * (z : C2).fst) :=
    hphaseScalar.mul contDiff_const
  have hsecond : ContDiff ℝ ∞
      (fun t : ℝ ↦ Complex.exp (t * Complex.I) * (z : C2).snd) :=
    hphaseScalar.mul contDiff_const
  have hphasePair : ContDiff ℝ ∞ (fun t : ℝ ↦
      (Complex.exp (t * Complex.I) * (z : C2).fst,
        Complex.exp (t * Complex.I) * (z : C2).snd)) :=
    hfirst.prodMk hsecond
  have hambient : @ContDiff ℝ inferInstance ℝ inferInstance inferInstance C2 inferInstance
      WithLp.instProdInnerProductSpace.toNormedSpace ∞
      (fun t : ℝ ↦ WithLp.toLp 2
        (Complex.exp (t * Complex.I) * (z : C2).fst,
          Complex.exp (t * Complex.I) * (z : C2).snd)) := by
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.contDiff.comp hphasePair
  have hsmooth : ContMDiff 𝓘(ℝ) (𝓡 3) ∞ (sphere3_phase_curve z) := by
    unfold sphere3_phase_curve
    apply ContMDiff.codRestrict_sphere (n := 3)
    exact hambient.contMDiff
  refine ⟨hsmooth, ?_⟩
  intro t hzero
  have hphase : MDifferentiableAt 𝓘(ℝ) (𝓡 3) (sphere3_phase_curve z) t :=
    hsmooth.mdifferentiableAt (by simp)
  have hcoe : MDifferentiableAt (𝓡 3) 𝓘(ℝ, C2)
      ((↑) : unitSphere3 → C2) (sphere3_phase_curve z t) :=
    (contMDiff_coe_sphere (E := C2) (m := ∞)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp_apply t hcoe hphase
    (show TangentSpace 𝓘(ℝ) t from (1 : ℝ))
  have hcomp : (((↑) : unitSphere3 → C2) ∘ sphere3_phase_curve z) =
      (fun s : ℝ ↦ WithLp.toLp 2
        (Complex.exp (s * Complex.I) * (z : C2).fst,
          Complex.exp (s * Complex.I) * (z : C2).snd)) := by
    funext s
    rfl
  have hambient_zero :
      mfderiv 𝓘(ℝ) 𝓘(ℝ, C2)
        (((↑) : unitSphere3 → C2) ∘ sphere3_phase_curve z) t (1 : ℝ) = 0 := by
    rw [hchain, hzero, map_zero]
    rfl
  have hscalarDeriv : HasDerivAt (fun s : ℝ ↦ Complex.exp (s * Complex.I))
      (Complex.exp (t * Complex.I) * Complex.I) t := by
    simpa [Complex.ofRealCLM_apply] using
      (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp)
  have hpairDeriv : HasDerivAt (fun s : ℝ ↦
      (Complex.exp (s * Complex.I) * (z : C2).fst,
        Complex.exp (s * Complex.I) * (z : C2).snd))
      ((Complex.exp (t * Complex.I) * Complex.I) * (z : C2).fst,
        (Complex.exp (t * Complex.I) * Complex.I) * (z : C2).snd) t :=
    (hscalarDeriv.mul_const _).prodMk (hscalarDeriv.mul_const _)
  have hderiv : HasDerivAt
      (fun s : ℝ ↦ WithLp.toLp 2
        (Complex.exp (s * Complex.I) * (z : C2).fst,
          Complex.exp (s * Complex.I) * (z : C2).snd))
      (WithLp.toLp 2
        ((Complex.exp (t * Complex.I) * Complex.I) * (z : C2).fst,
          (Complex.exp (t * Complex.I) * Complex.I) * (z : C2).snd)) t := by
    simpa [Function.comp_def] using
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.hasFDerivAt.comp_hasDerivAt t
        hpairDeriv)
  have hambient_value :
      mfderiv 𝓘(ℝ) 𝓘(ℝ, C2)
          (fun s : ℝ ↦ WithLp.toLp 2
            (Complex.exp (s * Complex.I) * (z : C2).fst,
              Complex.exp (s * Complex.I) * (z : C2).snd)) t (1 : ℝ) =
        WithLp.toLp 2
          ((Complex.exp (t * Complex.I) * Complex.I) * (z : C2).fst,
            (Complex.exp (t * Complex.I) * Complex.I) * (z : C2).snd) := by
    rw [mfderiv_eq_fderiv]
    change deriv (fun s : ℝ ↦ WithLp.toLp 2
      (Complex.exp (s * Complex.I) * (z : C2).fst,
        Complex.exp (s * Complex.I) * (z : C2).snd)) t = _
    exact hderiv.deriv
  rw [hcomp, hambient_value] at hambient_zero
  have hscalar_ne : Complex.exp (t * Complex.I) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero
  apply ne_zero_of_mem_unit_sphere z
  apply WithLp.ofLp_injective
  apply Prod.ext
  · have hfst := congrArg WithLp.fst hambient_zero
    change (Complex.exp (t * Complex.I) * Complex.I) * (z : C2).fst = 0 at hfst
    exact (mul_eq_zero.mp hfst).resolve_left hscalar_ne
  · have hsnd := congrArg WithLp.snd hambient_zero
    change (Complex.exp (t * Complex.I) * Complex.I) * (z : C2).snd = 0 at hsnd
    exact (mul_eq_zero.mp hsnd).resolve_left hscalar_ne
