import PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ClippedDuhamelOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.VectorDuhamelBoundedLinear
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open MorganTianLib.ParabolicPDE Set MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- The actual six-component Duhamel value map is a bounded linear operator. -/
theorem exists_vector_duhamel_boundedLinear (T : ℝ) (hT : 0 ≤ T) :
    ∃ D : ((ℝ × E3) →ᵇ E6) →L[ℝ] (Slab T →ᵇ E6),
      ‖D‖ ≤ 6*T ∧ ∀ (F : (ℝ × E3) →ᵇ E6) (p : Slab T) (k : Fin 6),
        (D F p) k = ∫ s in (0:ℝ)..(p.1:ℝ), ∫ y : E3,
          euclideanHeatKernel 3 ((p.1:ℝ)-s) (p.2-y)*(F (s,y) k) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨S, hS, hSbound, _hSlip⟩ := clipped_duhamel_operator T hT
  let clip (q : ℝ × E3) : ℝ := max 0 (min T q.1)
  let K : E3 → ℝ := fun z => euclideanHeatKernel 3 1 z
  have hKint : Integrable K volume :=
    ((euclideanHeatKernel_mass_semigroup 3).1 1 (by norm_num)).1
  have hKpos (z : E3) : 0 < K z :=
    euclideanHeatKernel_pos 3 (by norm_num) z
  have hKcont : Continuous K := by
    exact (euclideanHeatKernel_three_heat_equation (by norm_num)).1.continuous

  have hSfixed (g : (ℝ × E3) →ᵇ ℝ) (q : ℝ × E3) :
      S g q = clip q * ∫ r in (0:ℝ)..1,
        ∫ z : E3, K z * g (clip q * r,
          q.2 - √(clip q * (1-r)) • z) := by
    rw [hS g q]
    simpa [clip, K] using
      (duhamel_fixed_domain_formula g (clip q) (le_max_left 0 (min T q.1)) q.2)

  let I (g : (ℝ × E3) →ᵇ ℝ) (q : ℝ × E3) (r : ℝ) : ℝ :=
    ∫ z : E3, K z * g (clip q * r, q.2 - √(clip q * (1-r)) • z)
  have hArg (q : ℝ × E3) (r : ℝ) :
      Continuous (fun z : E3 =>
        (clip q * r, q.2 - √(clip q * (1-r)) • z)) := by
    fun_prop
  have hIint (g : (ℝ × E3) →ᵇ ℝ) (q : ℝ × E3) (r : ℝ) :
      Integrable (fun z : E3 => K z *
        g (clip q * r, q.2 - √(clip q * (1-r)) • z)) volume := by
    apply Integrable.mul_bdd hKint
      ((g.continuous.comp (hArg q r)).aestronglyMeasurable)
    filter_upwards [] with z
    exact BoundedContinuousFunction.norm_coe_le_norm g _
  have hIcont (g : (ℝ × E3) →ᵇ ℝ) (q : ℝ × E3) : Continuous (I g q) := by
    let φ : ℝ → E3 → ℝ := fun r z =>
      K z * g (clip q * r, q.2 - √(clip q * (1-r)) • z)
    have hmeas : ∀ r : ℝ, AEStronglyMeasurable (φ r) volume := by
      intro r
      have hz : Continuous (fun z : E3 =>
          (clip q * r, q.2 - √(clip q * (1-r)) • z)) := hArg q r
      exact (hKcont.mul (g.continuous.comp hz)).aestronglyMeasurable
    have hbound : ∀ r : ℝ, ∀ᵐ z ∂volume, ‖φ r z‖ ≤ K z * ‖g‖ := by
      intro r
      filter_upwards [] with z
      dsimp [φ]
      calc
        ‖K z * g (clip q * r, q.2 - √(clip q * (1-r)) • z)‖ =
            ‖K z‖ * ‖g (clip q * r, q.2 - √(clip q * (1-r)) • z)‖ := norm_mul _ _
        _ = K z * ‖g (clip q * r, q.2 - √(clip q * (1-r)) • z)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hKpos z))]
        _ ≤ K z * ‖g‖ :=
          mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm g _)
            (le_of_lt (hKpos z))
    have hdom : Integrable (fun z : E3 => K z * ‖g‖) volume :=
      Integrable.mul_const hKint ‖g‖
    have hcont : ∀ᵐ z ∂volume, Continuous (fun r : ℝ => φ r z) := by
      filter_upwards [] with z
      have hr : Continuous (fun r : ℝ =>
          (clip q * r, q.2 - √(clip q * (1-r)) • z)) := by
        fun_prop
      exact continuous_const.mul (g.continuous.comp hr)
    simpa [I, φ] using
      (MeasureTheory.continuous_of_dominated hmeas hbound hdom hcont)

  have hIadd (g₁ g₂ : (ℝ × E3) →ᵇ ℝ) (q : ℝ × E3) (r : ℝ) :
      I (g₁ + g₂) q r = I g₁ q r + I g₂ q r := by
    dsimp [I]
    calc
      (∫ z : E3, K z * (g₁ + g₂)
          (clip q * r, q.2 - √(clip q * (1-r)) • z)) =
        ∫ z : E3, (K z * g₁
            (clip q * r, q.2 - √(clip q * (1-r)) • z)) +
          (K z * g₂ (clip q * r, q.2 - √(clip q * (1-r)) • z)) := by
            congr 1
            funext z
            simp [mul_add]
      _ = (∫ z : E3, K z * g₁
            (clip q * r, q.2 - √(clip q * (1-r)) • z)) +
          ∫ z : E3, K z * g₂
            (clip q * r, q.2 - √(clip q * (1-r)) • z) :=
          integral_add (hIint g₁ q r) (hIint g₂ q r)
  have hIsmul (a : ℝ) (g : (ℝ × E3) →ᵇ ℝ) (q : ℝ × E3) (r : ℝ) :
      I (a • g) q r = a • I g q r := by
    dsimp [I]
    calc
      (∫ z : E3, K z * (a • g)
          (clip q * r, q.2 - √(clip q * (1-r)) • z)) =
        ∫ z : E3, a • (K z * g
          (clip q * r, q.2 - √(clip q * (1-r)) • z)) := by
            congr 1
            funext z
            simp [smul_eq_mul, mul_left_comm, mul_comm]
      _ = a • ∫ z : E3, K z * g
            (clip q * r, q.2 - √(clip q * (1-r)) • z) := integral_smul a _

  have hSadd (g₁ g₂ : (ℝ × E3) →ᵇ ℝ) : S (g₁ + g₂) = S g₁ + S g₂ := by
    apply BoundedContinuousFunction.ext
    intro q
    change S (g₁ + g₂) q = S g₁ q + S g₂ q
    rw [hSfixed (g₁ + g₂) q, hSfixed g₁ q, hSfixed g₂ q]
    have hfun : (fun r : ℝ => I (g₁ + g₂) q r) =
        fun r => I g₁ q r + I g₂ q r := funext (hIadd g₁ g₂ q)
    rw [hfun, intervalIntegral.integral_add
      ((hIcont g₁ q).intervalIntegrable 0 1)
      ((hIcont g₂ q).intervalIntegrable 0 1)]
    ring
  have hSsmul (a : ℝ) (g : (ℝ × E3) →ᵇ ℝ) : S (a • g) = a • S g := by
    apply BoundedContinuousFunction.ext
    intro q
    change S (a • g) q = a • S g q
    rw [hSfixed (a • g) q, hSfixed g q]
    have hfun : (fun r : ℝ => I (a • g) q r) = fun r => a • I g q r :=
      funext (hIsmul a g q)
    rw [hfun, intervalIntegral.integral_smul]
    change clip q * (a * (∫ r in (0:ℝ)..1, I g q r)) =
      a * (clip q * ∫ r in (0:ℝ)..1, I g q r)
    ring

  have hproj (k : Fin 6) : Continuous (fun v : E6 => v k) :=
    (EuclideanSpace.proj k).continuous
  have hcoordinate (v : E6) (k : Fin 6) : ‖v k‖ ≤ ‖v‖ := by
    have hsq : ‖v k‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun i : Fin 6 => ‖v i‖ ^ 2)
        (fun i hi => sq_nonneg (‖v i‖)) (Finset.mem_univ k)
    nlinarith [hsq, norm_nonneg (v k), norm_nonneg v]
  let coord : ((ℝ × E3) →ᵇ E6) → Fin 6 → ((ℝ × E3) →ᵇ ℝ) := fun F k =>
    BoundedContinuousFunction.ofNormedAddCommGroup (fun q => F q k)
      ((hproj k).comp F.continuous) ‖F‖ (by
        intro q
        exact (hcoordinate (F q) k).trans
          (BoundedContinuousFunction.norm_coe_le_norm F q))
  have hcoordBound (F : (ℝ × E3) →ᵇ E6) (k : Fin 6) (q : ℝ × E3) :
      ‖coord F k q‖ ≤ ‖F‖ := by
    change ‖F q k‖ ≤ ‖F‖
    exact (hcoordinate (F q) k).trans (BoundedContinuousFunction.norm_coe_le_norm F q)
  have hcoordNorm (F : (ℝ × E3) →ᵇ E6) (k : Fin 6) :
      ‖coord F k‖ ≤ ‖F‖ := by
    dsimp [coord]
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      ((hproj k).comp F.continuous) (norm_nonneg _) (fun q =>
        (hcoordinate (F q) k).trans (BoundedContinuousFunction.norm_coe_le_norm F q))
  have hcoordAdd (F G : (ℝ × E3) →ᵇ E6) (k : Fin 6) :
      coord (F + G) k = coord F k + coord G k := by
    apply BoundedContinuousFunction.ext
    intro q
    rfl
  have hcoordSmul (a : ℝ) (F : (ℝ × E3) →ᵇ E6) (k : Fin 6) :
      coord (a • F) k = a • coord F k := by
    apply BoundedContinuousFunction.ext
    intro q
    rfl

  have hnormCoord (v : E6) : ‖v‖ ≤ ∑ k : Fin 6, ‖v k‖ := by
    calc
      ‖v‖ = ‖∑ k : Fin 6, EuclideanSpace.single k (v k)‖ := by
        congr 1
        ext j
        simp
      _ ≤ ∑ k : Fin 6, ‖EuclideanSpace.single k (v k)‖ :=
        norm_sum_le (Finset.univ : Finset (Fin 6)) _
      _ = ∑ k : Fin 6, ‖v k‖ := by simp

  have hscalarPointBound (F : (ℝ × E3) →ᵇ E6) (k : Fin 6) (q : ℝ × E3) :
      ‖S (coord F k) q‖ ≤ T * ‖F‖ := by
    calc
      ‖S (coord F k) q‖ ≤ ‖S (coord F k)‖ :=
        BoundedContinuousFunction.norm_coe_le_norm (S (coord F k)) q
      _ ≤ T * ‖coord F k‖ := hSbound (coord F k)
      _ ≤ T * ‖F‖ := mul_le_mul_of_nonneg_left (hcoordNorm F k) hT

  have hvalPiCont (F : (ℝ × E3) →ᵇ E6) :
      Continuous (fun p : Slab T => fun k : Fin 6 =>
        S (coord F k) ((p.1 : ℝ), p.2)) := by
    apply continuous_pi
    intro k
    have hp : Continuous (fun p : Slab T => ((p.1 : ℝ), p.2)) :=
      Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd
    exact (S (coord F k)).continuous.comp hp
  let val (F : (ℝ × E3) →ᵇ E6) (p : Slab T) : E6 :=
    WithLp.toLp 2 (fun k : Fin 6 => S (coord F k) ((p.1 : ℝ), p.2))
  have hvalCont (F : (ℝ × E3) →ᵇ E6) : Continuous (val F) := by
    exact ((EuclideanSpace.equiv (Fin 6) ℝ).symm).continuous.comp (hvalPiCont F)
  have hvalBound (F : (ℝ × E3) →ᵇ E6) (p : Slab T) :
      ‖val F p‖ ≤
        (6*T) * ‖F‖ := by
    calc
      ‖val F p‖ ≤ ∑ k : Fin 6, ‖S (coord F k) ((p.1 : ℝ), p.2)‖ := by
        exact hnormCoord (val F p)
      _ ≤ ∑ k : Fin 6, T * ‖F‖ :=
        Finset.sum_le_sum (fun k _ => hscalarPointBound F k ((p.1 : ℝ), p.2))
      _ = (6*T) * ‖F‖ := by simp [Finset.sum_const, Fintype.card_fin]; ring
  let out : ((ℝ × E3) →ᵇ E6) → ((Slab T) →ᵇ E6) := fun F =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (val F) (hvalCont F) ((6*T) * ‖F‖) (hvalBound F)
  have houtAdd (F G : (ℝ × E3) →ᵇ E6) : out (F + G) = out F + out G := by
    apply BoundedContinuousFunction.ext
    intro p
    ext k
    change S (coord (F + G) k) ((p.1 : ℝ), p.2) =
      S (coord F k) ((p.1 : ℝ), p.2) + S (coord G k) ((p.1 : ℝ), p.2)
    rw [hcoordAdd F G k, hSadd]
    rfl
  have houtSmul (a : ℝ) (F : (ℝ × E3) →ᵇ E6) : out (a • F) = a • out F := by
    apply BoundedContinuousFunction.ext
    intro p
    ext k
    change S (coord (a • F) k) ((p.1 : ℝ), p.2) =
      a • S (coord F k) ((p.1 : ℝ), p.2)
    rw [hcoordSmul a F k, hSsmul]
    rfl
  let L : ((ℝ × E3) →ᵇ E6) →ₗ[ℝ] (Slab T →ᵇ E6) :=
    { toFun := out
      map_add' := houtAdd
      map_smul' := houtSmul }
  have houtNorm (F : (ℝ × E3) →ᵇ E6) : ‖L F‖ ≤ (6*T) * ‖F‖ := by
    dsimp [L, out]
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le (hvalCont F)
      (mul_nonneg (mul_nonneg (by norm_num) hT) (norm_nonneg _)) (hvalBound F)
  let D : ((ℝ × E3) →ᵇ E6) →L[ℝ] (Slab T →ᵇ E6) :=
    L.mkContinuous (6*T) (by intro F; simpa [mul_assoc] using houtNorm F)
  have hDnorm : ‖D‖ ≤ 6*T :=
    LinearMap.mkContinuous_norm_le L (mul_nonneg (by norm_num) hT)
      (by intro F; simpa [mul_assoc] using houtNorm F)

  have hvalue (F : (ℝ × E3) →ᵇ E6) (p : Slab T) (k : Fin 6) :
      (D F p) k = ∫ s in (0:ℝ)..(p.1:ℝ), ∫ y : E3,
        euclideanHeatKernel 3 ((p.1:ℝ)-s) (p.2-y)*(F (s,y) k) := by
    change S (coord F k) ((p.1 : ℝ), p.2) = _
    rw [hS (coord F k) ((p.1 : ℝ), p.2)]
    rw [min_eq_right p.1.property.2, max_eq_right p.1.property.1]
    have hchange (s t : ℝ) (x : E3) :
        (∫ y : E3, euclideanHeatKernel 3 (t-s) y * coord F k (s,x-y)) =
          ∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * coord F k (s,y) := by
      let g : E3 → ℝ := fun y =>
        euclideanHeatKernel 3 (t-s) (x-y) * coord F k (s,y)
      have hcomp :=
        (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
          (MeasurableEquiv.subLeft x).measurableEmbedding g
      calc
        (∫ y : E3, euclideanHeatKernel 3 (t-s) y * coord F k (s,x-y)) =
            ∫ y : E3, g (x-y) := by
              congr 1
              funext y
              simp [g]
        _ = ∫ y : E3, g y := hcomp
        _ = ∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * coord F k (s,y) := rfl
    apply intervalIntegral.integral_congr
    intro s hs
    simpa [coord] using hchange s (p.1:ℝ) p.2

  have hzero (hT0 : T = 0) : D = 0 := by
    apply ContinuousLinearMap.ext
    intro F
    apply BoundedContinuousFunction.ext
    intro p
    ext k
    apply norm_eq_zero.mp
    apply le_antisymm
    · calc
      ‖(D F p) k‖ ≤ ‖D F p‖ := hcoordinate (D F p) k
      _ ≤ ‖D F‖ := BoundedContinuousFunction.norm_coe_le_norm (D F) p
      _ ≤ ‖D‖ * ‖F‖ := ContinuousLinearMap.le_opNorm D F
      _ = 0 := by
        have hz : ‖D‖ = 0 := by
          apply le_antisymm
          · simpa [hT0] using hDnorm
          · exact norm_nonneg _
        simp [hz]
    · exact norm_nonneg _
  refine ⟨D, hDnorm, ?_⟩
  intro F p k
  exact hvalue F p k
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.VectorDuhamelBoundedLinear
