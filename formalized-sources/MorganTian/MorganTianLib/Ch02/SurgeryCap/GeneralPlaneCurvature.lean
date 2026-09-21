import MorganTianLib.Ch02.SurgeryCap.WarpedHorizontalCurvature
import MorganTianLib.Ch02.SurgeryCap.WarpedRadialCurvature
open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [SigmaCompactSpace N] [T2Space N]
/-- **Math.** The actual warped curvature on arbitrary radial-horizontal planes,
without a constant-curvature assumption on the base. -/
theorem warpedConnection_general_plane_curvature (g : RiemannianMetric I N)
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) (hp : ∀ r, 0 < r → 0 < w r)
    (X Y : SmoothVectorField I N) (a b : ℝ) (q : N × ↥positiveReal) :
    let R := coneRadialField (I := I) (N := N)
    let U := coneHorizontalLift X + SmoothVectorField.smul (fun _ => a) contMDiff_const R
    let V := coneHorizontalLift Y + SmoothVectorField.smul (fun _ => b) contMDiff_const R
    let G := warpedMetric g w hw hp
    G.metricInner q ((warpedConnection g w hw hp).curvature U V U q) (V q) =
      w q.2 ^ 2 * g.metricInner q.1 ((leviCivitaConnectionGeneral g).curvature X Y X q.1) (Y q.1) -
      w q.2 ^ 2 * deriv w q.2 ^ 2 *
        (g.metricInner q.1 (X q.1) (X q.1) * g.metricInner q.1 (Y q.1) (Y q.1) -
          g.metricInner q.1 (X q.1) (Y q.1) ^ 2) -
      w q.2 * deriv (deriv w) q.2 *
        g.metricInner q.1 (b • X q.1 - a • Y q.1) (b • X q.1 - a • Y q.1) := by
/- SWARM_PROOF_BEGIN -/
  let G := warpedMetric g w hw hp
  let nabla := warpedConnection g w hw hp
  let R : SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) :=
    coneRadialField (I := I) (N := N)
  let HX := coneHorizontalLift X
  let HY := coneHorizontalLift Y
  let ha : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun _ : N × ↥positiveReal => a) := contMDiff_const
  let hb : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun _ : N × ↥positiveReal => b) := contMDiff_const
  let aR := SmoothVectorField.smul (fun _ : N × ↥positiveReal => a) ha R
  let bR := SmoothVectorField.smul (fun _ : N × ↥positiveReal => b) hb R
  have hLC : nabla.IsLeviCivita G := by
    exact warpedConnection_isLeviCivita g w hw hp
  let F := fun (A B C D : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
      (N × ↥positiveReal)) =>
      G.metricInner q ((nabla.curvature A B C) q) (D q)
  have hF_add₁ (A B C D E : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
      (N × ↥positiveReal)) :
      F (A + B) C D E = F A C D E + F B C D E := by
    simp only [F]
    rw [nabla.curvature_add_left]
    simp only [RiemannianMetric.metricInner_add_left]
  have hF_add₂ (A B C D E : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
      (N × ↥positiveReal)) :
      F A (B + C) D E = F A B D E + F A C D E := by
    simp only [F]
    rw [nabla.curvature_add_middle]
    simp only [RiemannianMetric.metricInner_add_left]
  have hF_add₃ (A B C D E : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
      (N × ↥positiveReal)) :
      F A B (C + D) E = F A B C E + F A B D E := by
    simp only [F]
    rw [nabla.curvature_add_right]
    simp only [RiemannianMetric.metricInner_add_left]
  have hF_add₄ (A B C D E : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
      (N × ↥positiveReal)) :
      F A B C (D + E) = F A B C D + F A B C E := by
    change G.metricInner q ((nabla.curvature A B C) q) (D q + E q) = _
    rw [G.metricInner_add_right]
  have hF_smul₁ (f : (N × ↥positiveReal) → ℝ)
      (hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f)
      (A B C D : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
        (N × ↥positiveReal)) :
      F (SmoothVectorField.smul f hf A) B C D = f q * F A B C D := by
    simp only [F]
    rw [nabla.curvature_smul_left]
    simp only [RiemannianMetric.metricInner_smul_left]
  have hF_smul₂ (f : (N × ↥positiveReal) → ℝ)
      (hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f)
      (A B C D : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
        (N × ↥positiveReal)) :
      F A (SmoothVectorField.smul f hf B) C D = f q * F A B C D := by
    simp only [F]
    rw [nabla.curvature_smul_middle]
    simp only [RiemannianMetric.metricInner_smul_left]
  have hF_smul₃ (f : (N × ↥positiveReal) → ℝ)
      (hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f)
      (A B C D : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
        (N × ↥positiveReal)) :
      F A B (SmoothVectorField.smul f hf C) D = f q * F A B C D := by
    simp only [F]
    rw [nabla.curvature_smul_right]
    simp only [RiemannianMetric.metricInner_smul_left]
  have hF_smul₄ (f : (N × ↥positiveReal) → ℝ)
      (hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f)
      (A B C D : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
        (N × ↥positiveReal)) :
      F A B C (SmoothVectorField.smul f hf D) = f q * F A B C D := by
    change G.metricInner q ((nabla.curvature A B C) q) (f q • D q) = _
    rw [G.metricInner_smul_right]
  have hHoriz : nabla.curvatureForm G HX HY HX HY q =
      w q.2 ^ 2 * g.metricInner q.1
          ((leviCivitaConnectionGeneral g).curvature X Y X q.1) (Y q.1) -
        w q.2 ^ 2 * deriv w q.2 ^ 2 *
          (g.metricInner q.1 (X q.1) (X q.1) *
            g.metricInner q.1 (Y q.1) (Y q.1) -
            g.metricInner q.1 (X q.1) (Y q.1) ^ 2) := by
    change (warpedMetric g w hw hp).metricInner q
      (((warpedConnection g w hw hp).curvature
        (coneHorizontalLift X) (coneHorizontalLift Y)
        (coneHorizontalLift X)) q)
      ((coneHorizontalLift Y) q) = _
    rw [warpedConnection_horizontal_curvature,
      warpedMetric_metricInner_prod]
    simp [coneHorizontalLift_apply]
    have hsym : (g.inner q.1) (Y q.1) (X q.1) =
        (g.inner q.1) (X q.1) (Y q.1) :=
      g.metricInner_comm q.1 (Y q.1) (X q.1)
    rw [hsym]
    ring
  have hRad (A B : SmoothVectorField I N) :
      nabla.curvatureForm G (coneHorizontalLift A) R R
          (coneHorizontalLift B) q =
        w q.2 * deriv (deriv w) q.2 *
          g.metricInner q.1 (A q.1) (B q.1) := by
    change (warpedMetric g w hw hp).metricInner q
      (((warpedConnection g w hw hp).curvature
        (coneHorizontalLift A) (coneRadialField (I := I) (N := N))
        (coneRadialField (I := I) (N := N))) q)
      ((coneHorizontalLift B) q) = _
    rw [warpedConnection_radial_curvature,
      warpedMetric_metricInner_prod]
    simp [coneHorizontalLift_apply]
    field_simp [ne_of_gt (hp _ q.2.property)]
  have hZero (A B C : SmoothVectorField I N) :
      nabla.curvatureForm G (coneHorizontalLift A) (coneHorizontalLift B)
          (coneHorizontalLift C) R q = 0 := by
    change (warpedMetric g w hw hp).metricInner q
      (((warpedConnection g w hw hp).curvature
        (coneHorizontalLift A) (coneHorizontalLift B)
        (coneHorizontalLift C)) q)
      (coneRadialField (I := I) (N := N) q) = 0
    rw [warpedConnection_horizontal_curvature,
      warpedMetric_metricInner_prod]
    simp [coneRadialField_apply]
  have hantiL (A B C D : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
      (N × ↥positiveReal)) :
      nabla.curvatureForm G A B C D q =
        -nabla.curvatureForm G B A C D q := by
    exact nabla.curvatureForm_antisymm_left G A B C D q
  have hantiR (A B C D : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
      (N × ↥positiveReal)) :
      nabla.curvatureForm G A B C D q =
        -nabla.curvatureForm G A B D C q := by
    exact nabla.curvatureForm_antisymm_right G hLC.2 A B C D q
  have hpair (A B C D : SmoothVectorField (I.prod 𝓘(ℝ, ℝ))
      (N × ↥positiveReal)) :
      nabla.curvatureForm G A B C D q =
        nabla.curvatureForm G C D A B q := by
    exact nabla.curvatureForm_pairSwap G hLC.1 hLC.2 A B C D q
  have hExpand :
      F (HX + aR) (HY + bR) (HX + aR) (HY + bR) =
        F HX HY HX HY +
          b * F HX HY HX R +
          a * F HX HY R HY +
          (a * b) * F HX HY R R +
          b * F HX R HX HY +
          (b ^ 2) * F HX R HX R +
          (a * b) * F HX R R HY +
          (a * b ^ 2) * F HX R R R +
          a * F R HY HX HY +
          (a * b) * F R HY HX R +
          (a ^ 2) * F R HY R HY +
          (a ^ 2 * b) * F R HY R R +
          (a * b) * F R R HX HY +
          (a * b ^ 2) * F R R HX R +
          (a ^ 2 * b) * F R R R HY +
          (a ^ 2 * b ^ 2) * F R R R R := by
    simp only [aR, bR, hF_add₁, hF_add₂, hF_add₃, hF_add₄,
      hF_smul₁, hF_smul₂, hF_smul₃, hF_smul₄]
    ring
  have hzero₁ : nabla.curvatureForm G HX HY HX R q = 0 := by
    exact hZero X Y X
  have hzero₂ : nabla.curvatureForm G HX HY R HY q = 0 := by
    rw [hantiR HX HY R HY, hZero X Y Y]
    ring
  have hzero₃ : nabla.curvatureForm G HX HY R R q = 0 := by
    rw [hpair HX HY R R]
    have h := hantiL R R HX HY
    linarith
  have hzero₄ : nabla.curvatureForm G HX R HX HY q = 0 := by
    rw [hpair HX R HX HY, hzero₁]
  have hxx : nabla.curvatureForm G HX R HX R q =
      -(w q.2 * deriv (deriv w) q.2 *
        g.metricInner q.1 (X q.1) (X q.1)) := by
    rw [hantiR HX R HX R, hRad X X]
  have hxy : nabla.curvatureForm G HX R R HY q =
      w q.2 * deriv (deriv w) q.2 *
        g.metricInner q.1 (X q.1) (Y q.1) := hRad X Y
  have hzero₅ : nabla.curvatureForm G HX R R R q = 0 := by
    have h := hantiR HX R R R
    linarith
  have hzero₆ : nabla.curvatureForm G R HY HX HY q = 0 := by
    rw [hpair R HY HX HY, hzero₂]
  have hcross : nabla.curvatureForm G R HY HX R q =
      w q.2 * deriv (deriv w) q.2 *
        g.metricInner q.1 (X q.1) (Y q.1) := by
    rw [hpair R HY HX R]
    exact hxy
  have hyy : nabla.curvatureForm G R HY R HY q =
      -(w q.2 * deriv (deriv w) q.2 *
        g.metricInner q.1 (Y q.1) (Y q.1)) := by
    rw [hantiL R HY R HY, hRad Y Y]
  have hzero₇ : nabla.curvatureForm G R HY R R q = 0 := by
    have h := hantiR R HY R R
    linarith
  have hzero₈ : nabla.curvatureForm G R R HX HY q = 0 := by
    have h := hantiL R R HX HY
    linarith
  have hzero₉ : nabla.curvatureForm G R R HX R q = 0 := by
    have h := hantiL R R HX R
    linarith
  have hzero₁₀ : nabla.curvatureForm G R R R HY q = 0 := by
    have h := hantiL R R R HY
    linarith
  have hzero₁₁ : nabla.curvatureForm G R R R R q = 0 := by
    have h := hantiL R R R R
    linarith
  change F (HX + aR) (HY + bR) (HX + aR) (HY + bR) = _
  rw [hExpand]
  change
    nabla.curvatureForm G HX HY HX HY q +
        b * nabla.curvatureForm G HX HY HX R q +
        a * nabla.curvatureForm G HX HY R HY q +
        (a * b) * nabla.curvatureForm G HX HY R R q +
        b * nabla.curvatureForm G HX R HX HY q +
        (b ^ 2) * nabla.curvatureForm G HX R HX R q +
        (a * b) * nabla.curvatureForm G HX R R HY q +
        (a * b ^ 2) * nabla.curvatureForm G HX R R R q +
        a * nabla.curvatureForm G R HY HX HY q +
        (a * b) * nabla.curvatureForm G R HY HX R q +
        (a ^ 2) * nabla.curvatureForm G R HY R HY q +
        (a ^ 2 * b) * nabla.curvatureForm G R HY R R q +
        (a * b) * nabla.curvatureForm G R R HX HY q +
        (a * b ^ 2) * nabla.curvatureForm G R R HX R q +
        (a ^ 2 * b) * nabla.curvatureForm G R R R HY q +
        (a ^ 2 * b ^ 2) * nabla.curvatureForm G R R R R q = _
  rw [hzero₁, hzero₂, hzero₃, hzero₄, hxx, hxy, hzero₅,
    hzero₆, hcross, hyy, hzero₇, hzero₈, hzero₉, hzero₁₀, hzero₁₁,
    hHoriz]
  simp only [g.metricInner_sub_left, g.metricInner_sub_right,
    g.metricInner_smul_left, g.metricInner_smul_right]
  rw [g.metricInner_comm q.1 (Y q.1) (X q.1)]
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
