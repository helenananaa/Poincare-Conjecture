import MorganTianLib.Ch02.SurgeryCap.WarpedHorizontalConnection
import MorganTianLib.Ch02.SurgeryCap.WarpedRadialConnection
open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [SigmaCompactSpace N] [T2Space N]
/-- **Math.** The horizontal curvature of the actual warped Levi-Civita
connection, in the repository's do Carmo curvature convention. -/
theorem warpedConnection_horizontal_curvature (g : RiemannianMetric I N)
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) (hp : ∀ r, 0 < r → 0 < w r)
    (X Y Z : SmoothVectorField I N) (q : N × ↥positiveReal) :
    ((warpedConnection g w hw hp).curvature (coneHorizontalLift X)
      (coneHorizontalLift Y) (coneHorizontalLift Z)) q =
        (((leviCivitaConnectionGeneral g).curvature X Y Z) q.1 -
          (deriv w q.2)^2 •
            (g.metricInner q.1 (X q.1) (Z q.1) • Y q.1 -
              g.metricInner q.1 (Y q.1) (Z q.1) • X q.1), 0) := by
/- SWARM_PROOF_BEGIN -/
  let G := warpedMetric g w hw hp
  let nabla := warpedConnection g w hw hp
  let base := leviCivitaConnectionGeneral g
  let R : SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) :=
    coneRadialField (I := I) (N := N)
  let hX := coneHorizontalLift X
  let hY := coneHorizontalLift Y
  let hZ := coneHorizontalLift Z
  have hwc : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : N × ↥positiveReal => w (q.2 : ℝ)) :=
    hw.contMDiff.comp (contMDiff_subtype_val_opens.comp contMDiff_snd)
  have hwdc : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : N × ↥positiveReal => deriv w (q.2 : ℝ)) := by
    have hwd : ContDiff ℝ ∞ (deriv w) :=
      (contDiff_infty_iff_deriv.mp hw).2
    exact hwd.contMDiff.comp
      (contMDiff_subtype_val_opens.comp contMDiff_snd)
  have hpair (A B : SmoothVectorField I N) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun p => g.metricInner p (A p) (B p)) :=
    g.metricInner_field_contMDiff A B
  have hHHfield (A B : SmoothVectorField I N) :
      (fun q => G.metricInner q (coneHorizontalLift A q)
        (coneHorizontalLift B q)) =
        (fun q : N × ↥positiveReal =>
          w (q.2 : ℝ) ^ 2 * g.metricInner q.1 (A q.1) (B q.1)) := by
    funext q
    change (warpedMetric g w hw hp).metricInner q
      (coneHorizontalLift A q) (coneHorizontalLift B q) = _
    rw [warpedMetric_metricInner_prod]
    simp [coneHorizontalLift_apply]
  let pairXZ : N → ℝ := fun p => g.metricInner p (X p) (Z p)
  let pairYZ : N → ℝ := fun p => g.metricInner p (Y p) (Z p)
  let phiXZ : N × ↥positiveReal → ℝ := fun q =>
    -(w (q.2 : ℝ) * deriv w (q.2 : ℝ) * pairXZ q.1)
  let phiYZ : N × ↥positiveReal → ℝ := fun q =>
    -(w (q.2 : ℝ) * deriv w (q.2 : ℝ) * pairYZ q.1)
  have hphiXZ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ phiXZ := by
    dsimp [phiXZ, pairXZ]
    simpa [Function.comp_def, Pi.mul_apply, Pi.neg_apply] using
      ((hwc.mul hwdc).mul ((hpair X Z).comp contMDiff_fst)).neg
  have hphiYZ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ phiYZ := by
    dsimp [phiYZ, pairYZ]
    simpa [Function.comp_def, Pi.mul_apply, Pi.neg_apply] using
      ((hwc.mul hwdc).mul ((hpair Y Z).comp contMDiff_fst)).neg
  have hdirPhiXZ (A : SmoothVectorField I N) (q : N × ↥positiveReal) :
      (coneHorizontalLift A).dir phiXZ q =
        -(w (q.2 : ℝ) * deriv w (q.2 : ℝ)) *
          (A.dir (fun p => g.metricInner p (X p) (Z p)) q.1) := by
    rw [coneHorizontalLift_dir A hphiXZ q]
    change A.dir (fun p =>
      -(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
        g.metricInner p (X p) (Z p))) q.1 = _
    have hfun :
        (fun p => -(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
          g.metricInner p (X p) (Z p))) =
        (fun p => (-(w (q.2 : ℝ) * deriv w (q.2 : ℝ))) *
          g.metricInner p (X p) (Z p)) := by
      funext p
      ring
    rw [hfun, A.dir_const_mul _ q.1
      ((hpair X Z).mdifferentiableAt (by simp))]
  have hdirPhiYZ (A : SmoothVectorField I N) (q : N × ↥positiveReal) :
      (coneHorizontalLift A).dir phiYZ q =
        -(w (q.2 : ℝ) * deriv w (q.2 : ℝ)) *
          (A.dir (fun p => g.metricInner p (Y p) (Z p)) q.1) := by
    rw [coneHorizontalLift_dir A hphiYZ q]
    change A.dir (fun p =>
      -(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
        g.metricInner p (Y p) (Z p))) q.1 = _
    have hfun :
        (fun p => -(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
          g.metricInner p (Y p) (Z p))) =
        (fun p => (-(w (q.2 : ℝ) * deriv w (q.2 : ℝ))) *
          g.metricInner p (Y p) (Z p)) := by
      funext p
      ring
    rw [hfun, A.dir_const_mul _ q.1
      ((hpair Y Z).mdifferentiableAt (by simp))]
  have hcovXZfield :
      nabla.cov (coneHorizontalLift X) (coneHorizontalLift Z) =
        coneHorizontalLift (base.cov X Z) +
          SmoothVectorField.smul phiXZ hphiXZ R := by
    ext q
    rw [show nabla = warpedConnection g w hw hp from rfl,
      warpedConnection_horizontal_formula]
    change ((base.cov X Z) q.1,
        -(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
          g.metricInner q.1 (X q.1) (Z q.1))) =
      ((base.cov X Z) q.1, 0) +
        phiXZ q • ((0 : TangentSpace I q.1), (1 : ℝ))
    simp [phiXZ, pairXZ]
  have hcovYZfield :
      nabla.cov (coneHorizontalLift Y) (coneHorizontalLift Z) =
        coneHorizontalLift (base.cov Y Z) +
          SmoothVectorField.smul phiYZ hphiYZ R := by
    ext q
    rw [show nabla = warpedConnection g w hw hp from rfl,
      warpedConnection_horizontal_formula]
    change ((base.cov Y Z) q.1,
        -(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
          g.metricInner q.1 (Y q.1) (Z q.1))) =
      ((base.cov Y Z) q.1, 0) +
        phiYZ q • ((0 : TangentSpace I q.1), (1 : ℝ))
    simp [phiYZ, pairYZ]
  have hrad := warpedConnection_radial_formulas g w hw hp
  dsimp [nabla, R] at hrad ⊢
  let aH : TangentSpace I q.1 :=
    (base.cov Y (base.cov X Z)) q.1 -
      (deriv w q.2) ^ 2 •
        (g.metricInner q.1 (X q.1) (Z q.1) • Y q.1)
  let aR : ℝ :=
    -(w q.2 * deriv w q.2 *
        g.metricInner q.1 (Y q.1) ((base.cov X Z) q.1)) -
      w q.2 * deriv w q.2 *
        (Y.dir (fun p => g.metricInner p (X p) (Z p)) q.1)
  let bH : TangentSpace I q.1 :=
    (base.cov X (base.cov Y Z)) q.1 -
      (deriv w q.2) ^ 2 •
        (g.metricInner q.1 (Y q.1) (Z q.1) • X q.1)
  let bR : ℝ :=
    -(w q.2 * deriv w q.2 *
        g.metricInner q.1 (X q.1) ((base.cov Y Z) q.1)) -
      w q.2 * deriv w q.2 *
        (X.dir (fun p => g.metricInner p (Y p) (Z p)) q.1)
  let cH : TangentSpace I q.1 :=
    (base.cov (bracketField X Y) Z) q.1
  let cR : ℝ :=
    -(w q.2 * deriv w q.2 *
      g.metricInner q.1 ((bracketField X Y) q.1) (Z q.1))
  let aT : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q := (aH, aR)
  let bT : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q := (bH, bR)
  let cT : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q := (cH, cR)
  let dT : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q := (aH - bH, aR - bR)
  let outT : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q :=
    (aH - bH + cH, aR - bR + cR)
  have hprod_add (u v : TangentSpace I q.1) (a b : ℝ) :
      ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) +
          ((v, b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) =
        ((u + v, a + b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) := by
    rfl
  have hprod_smul (c : ℝ) (u : TangentSpace I q.1) (a : ℝ) :
      c • ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) =
        ((c • u, c • a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) := by
    rfl
  have hprod_ext (u v : TangentSpace I q.1) (a b : ℝ)
      (hu : u = v) (ha : a = b) :
      ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) =
        ((v, b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) := by
    rw [hu, ha]
  have hA :
      (nabla.cov (coneHorizontalLift Y)
        (nabla.cov (coneHorizontalLift X) (coneHorizontalLift Z))) q = aT := by
    rw [hcovXZfield, nabla.add_right, nabla.cov_smul_right hphiXZ]
    simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply]
    rw [warpedConnection_horizontal_formula,
      (hrad.2 Y q).1, hdirPhiXZ Y q]
    dsimp [phiXZ, pairXZ, R]
    change
      (((base.cov Y (base.cov X Z)) q.1,
          -(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
            g.metricInner q.1 (Y q.1) ((base.cov X Z) q.1))) :
        TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) +
        ((-(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
            g.metricInner q.1 (X q.1) (Z q.1)) •
            (((deriv w (q.2 : ℝ) / w (q.2 : ℝ)) • Y q.1, 0) :
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) q)) +
          ((-(w (q.2 : ℝ) * deriv w (q.2 : ℝ)) *
              Y.dir (fun p => g.metricInner p (X p) (Z p)) q.1) •
            ((0, 1) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q))) = aT
    rw [hprod_smul, hprod_smul, hprod_add]
    have hcoeff :
        (-(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
            g.inner q.1 (X q.1) (Z q.1))) *
            (deriv w (q.2 : ℝ) / w (q.2 : ℝ)) =
          -(deriv w (q.2 : ℝ)) ^ 2 *
            g.inner q.1 (X q.1) (Z q.1) := by
      field_simp [ne_of_gt (hp _ q.2.property)]
    apply hprod_ext
    · dsimp [aT, aH]
      simp only [smul_zero, add_zero]
      rw [smul_smul, hcoeff]
      module
    · dsimp [aT, aR]
      ring
  have hB :
      (nabla.cov (coneHorizontalLift X)
        (nabla.cov (coneHorizontalLift Y) (coneHorizontalLift Z))) q = bT := by
    rw [hcovYZfield, nabla.add_right, nabla.cov_smul_right hphiYZ]
    simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply]
    rw [warpedConnection_horizontal_formula,
      (hrad.2 X q).1, hdirPhiYZ X q]
    dsimp [phiYZ, pairYZ, R]
    change
      (((base.cov X (base.cov Y Z)) q.1,
          -(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
            g.metricInner q.1 (X q.1) ((base.cov Y Z) q.1))) :
        TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) +
        ((-(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
            g.metricInner q.1 (Y q.1) (Z q.1)) •
            (((deriv w (q.2 : ℝ) / w (q.2 : ℝ)) • X q.1, 0) :
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) q)) +
          ((-(w (q.2 : ℝ) * deriv w (q.2 : ℝ)) *
              X.dir (fun p => g.metricInner p (Y p) (Z p)) q.1) •
            ((0, 1) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q))) = bT
    rw [hprod_smul, hprod_smul, hprod_add]
    have hcoeff :
        (-(w (q.2 : ℝ) * deriv w (q.2 : ℝ) *
            g.inner q.1 (Y q.1) (Z q.1))) *
            (deriv w (q.2 : ℝ) / w (q.2 : ℝ)) =
          -(deriv w (q.2 : ℝ)) ^ 2 *
            g.inner q.1 (Y q.1) (Z q.1) := by
      field_simp [ne_of_gt (hp _ q.2.property)]
    apply hprod_ext
    · dsimp [bT, bH]
      simp only [smul_zero, add_zero]
      rw [smul_smul, hcoeff]
      module
    · dsimp [bT, bR]
      ring
  have hC :
      (nabla.cov (bracketField (coneHorizontalLift X)
        (coneHorizontalLift Y)) (coneHorizontalLift Z)) q = cT := by
    rw [bracketField_coneHorizontalLift_coneHorizontalLift,
      warpedConnection_horizontal_formula]
    try dsimp [cT, cH, cR]
  have hAB := congrArg₂
    (fun u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q => u - v) hA hB
  have hABC := congrArg₂
    (fun u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q => u + v) hAB hC
  have hSub : aT - bT = dT := by
    dsimp [aT, bT, dT]
    rfl
  have hAdd : dT + cT = outT := by
    dsimp [dT, cT, outT]
    rfl
  have hH : aH - bH + cH =
      ((base.curvature X Y Z) q.1 -
        (deriv w q.2) ^ 2 •
          (g.metricInner q.1 (X q.1) (Z q.1) • Y q.1 -
            g.metricInner q.1 (Y q.1) (Z q.1) • X q.1)) := by
    dsimp [aH, bH, cH]
    rw [base.curvature_apply]
    module
  have hR : aR - bR + cR = 0 := by
    dsimp [aR, bR, cR]
    have hcompat := (leviCivitaConnectionGeneral_isLeviCivita g).2
    have hYXZ := hcompat Y X Z q.1
    have hXYZ := hcompat X Y Z q.1
    have hsym := (leviCivitaConnectionGeneral_isLeviCivita g).1 X Y q.1
    have hsym_inner := congrArg (fun v => g.metricInner q.1 v (Z q.1)) hsym
    rw [g.metricInner_sub_left] at hsym_inner
    change
      Y.dir (fun p => g.inner p (X p) (Z p)) q.1 =
        g.inner q.1 ((leviCivitaConnectionGeneral g).cov Y X q.1) (Z q.1) +
          g.inner q.1 (X q.1) ((leviCivitaConnectionGeneral g).cov Y Z q.1) at hYXZ
    change
      X.dir (fun p => g.inner p (Y p) (Z p)) q.1 =
        g.inner q.1 ((leviCivitaConnectionGeneral g).cov X Y q.1) (Z q.1) +
          g.inner q.1 (Y q.1) ((leviCivitaConnectionGeneral g).cov X Z q.1) at hXYZ
    change
      g.inner q.1 ((leviCivitaConnectionGeneral g).cov X Y q.1) (Z q.1) -
          g.inner q.1 ((leviCivitaConnectionGeneral g).cov Y X q.1) (Z q.1) =
        g.inner q.1 (DCLieBracket X Y q.1) (Z q.1) at hsym_inner
    linear_combination
      -(w q.2 * deriv w q.2) * hYXZ +
        (w q.2 * deriv w q.2) * hXYZ +
        (w q.2 * deriv w q.2) * hsym_inner
  have hOut : outT =
      ((base.curvature X Y Z q.1 -
        (deriv w q.2) ^ 2 •
          (g.metricInner q.1 (X q.1) (Z q.1) • Y q.1 -
            g.metricInner q.1 (Y q.1) (Z q.1) • X q.1), 0) :
        TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) := by
    dsimp [outT]
    exact congrArg₂ (fun u : TangentSpace I q.1 => fun s : ℝ =>
      ((u, s) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q)) hH hR
  calc
    _ = (nabla.cov (coneHorizontalLift Y)
          (nabla.cov (coneHorizontalLift X) (coneHorizontalLift Z))) q -
        (nabla.cov (coneHorizontalLift X)
          (nabla.cov (coneHorizontalLift Y) (coneHorizontalLift Z))) q +
        (nabla.cov (bracketField (coneHorizontalLift X)
          (coneHorizontalLift Y)) (coneHorizontalLift Z)) q :=
      nabla.curvature_apply _ _ _ _
    _ = aT - bT + cT := hABC
    _ = dT + cT := congrArg (fun u => u + cT) hSub
    _ = outT := hAdd
    _ = _ := hOut
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
