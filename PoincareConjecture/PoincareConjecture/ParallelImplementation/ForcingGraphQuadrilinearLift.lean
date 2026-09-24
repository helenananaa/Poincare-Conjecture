import PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingGraphQuadrilinearLift
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
theorem exists_forcing_graph_quadrilinear_lift
    {A V Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (B : A →L[ℝ] A →L[ℝ] V →L[ℝ] V →L[ℝ] Z) (T alpha : ℝ) :
    ∃ Q : ForcingJet A T →L[ℝ] ForcingJet A T →L[ℝ]
        ForcingJet V T →L[ℝ] ForcingJet V T →L[ℝ] ForcingJet Z T,
      ‖Q‖ ≤ 8*‖B‖ ∧
      (∀ a b v w p, (Q a b v w).1 p = B (a.1 p) (b.1 p) (v.1 p) (w.1 p)) ∧
      (∀ a ∈ forcingGraph A T alpha, ∀ b ∈ forcingGraph A T alpha,
        ∀ v ∈ forcingGraph V T alpha, ∀ w ∈ forcingGraph V T alpha,
          Q a b v w ∈ forcingGraph Z T alpha) :=
/- SWARM_PROOF_BEGIN -/
by
  let firstRaw (a b : ForcingJet A T) (v w : ForcingJet V T)
      (p : Slab T) : Z := B (a.1 p) (b.1 p) (v.1 p) (w.1 p)
  let secondRaw (a b : ForcingJet A T) (v w : ForcingJet V T)
      (p : Pair T) : Z :=
    B (a.2 p) (b.1 p.1.1) (v.1 p.1.1) (w.1 p.1.1) +
    B (a.1 p.1.2) (b.2 p) (v.1 p.1.1) (w.1 p.1.1) +
    B (a.1 p.1.2) (b.1 p.1.2) (v.2 p) (w.1 p.1.1) +
    B (a.1 p.1.2) (b.1 p.1.2) (v.1 p.1.2) (w.2 p)

  have contFour {X : Type} [TopologicalSpace X]
      (f₁ : X → A) (f₂ : X → A) (f₃ : X → V) (f₄ : X → V)
      (h₁ : Continuous f₁) (h₂ : Continuous f₂)
      (h₃ : Continuous f₃) (h₄ : Continuous f₄) :
      Continuous (fun x => B (f₁ x) (f₂ x) (f₃ x) (f₄ x)) := by
    have h₁₂ : Continuous (fun x => B (f₁ x) (f₂ x)) :=
      B.continuous₂.comp (h₁.prodMk h₂)
    exact (h₁₂.clm_apply h₃).clm_apply h₄

  have hpair : Continuous (fun p : Pair T => (p.1 : Slab T × Slab T)) :=
    continuous_subtype_val
  have hleft : Continuous (fun p : Pair T => p.1.1) := continuous_fst.comp hpair
  have hright : Continuous (fun p : Pair T => p.1.2) := continuous_snd.comp hpair

  have firstCont (a b : ForcingJet A T) (v w : ForcingJet V T) :
      Continuous (firstRaw a b v w) := by
    exact contFour a.1 b.1 v.1 w.1 a.1.continuous b.1.continuous
      v.1.continuous w.1.continuous

  have secondCont (a b : ForcingJet A T) (v w : ForcingJet V T) :
      Continuous (secondRaw a b v w) := by
    dsimp [secondRaw]
    exact
      (((contFour a.2 (fun p : Pair T => b.1 p.1.1)
          (fun p : Pair T => v.1 p.1.1)
          (fun p : Pair T => w.1 p.1.1) a.2.continuous
          (b.1.continuous.comp hleft) (v.1.continuous.comp hleft)
          (w.1.continuous.comp hleft)).add
        (contFour (fun p : Pair T => a.1 p.1.2) b.2
          (fun p : Pair T => v.1 p.1.1)
          (fun p : Pair T => w.1 p.1.1) (a.1.continuous.comp hright)
          b.2.continuous (v.1.continuous.comp hleft)
          (w.1.continuous.comp hleft))).add
        (contFour (fun p : Pair T => a.1 p.1.2)
          (fun p : Pair T => b.1 p.1.2) v.2
          (fun p : Pair T => w.1 p.1.1) (a.1.continuous.comp hright)
          (b.1.continuous.comp hright) v.2.continuous
          (w.1.continuous.comp hleft))).add
        (contFour (fun p : Pair T => a.1 p.1.2)
          (fun p : Pair T => b.1 p.1.2)
          (fun p : Pair T => v.1 p.1.2) w.2 (a.1.continuous.comp hright)
          (b.1.continuous.comp hright) (v.1.continuous.comp hright)
          w.2.continuous)

  have jetFirstBoundA (x : ForcingJet A T) (p : Slab T) :
      ‖x.1 p‖ ≤ ‖x‖ := by
    exact (x.1.norm_coe_le_norm p).trans (norm_fst_le x)
  have jetSecondBoundA (x : ForcingJet A T) (p : Pair T) :
      ‖x.2 p‖ ≤ ‖x‖ := by
    exact (x.2.norm_coe_le_norm p).trans (norm_snd_le x)
  have jetFirstBoundV (x : ForcingJet V T) (p : Slab T) :
      ‖x.1 p‖ ≤ ‖x‖ := by
    exact (x.1.norm_coe_le_norm p).trans (norm_fst_le x)
  have jetSecondBoundV (x : ForcingJet V T) (p : Pair T) :
      ‖x.2 p‖ ≤ ‖x‖ := by
    exact (x.2.norm_coe_le_norm p).trans (norm_snd_le x)

  have Bbound (x y : A) (z u : V) :
      ‖B x y z u‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ * ‖z‖ * ‖u‖ := by
    calc
      ‖B x y z u‖ ≤ ‖B x y‖ * ‖z‖ * ‖u‖ := (B x y).le_opNorm₂ z u
      _ ≤ ‖B x‖ * ‖y‖ * ‖z‖ * ‖u‖ := by
        gcongr
        exact (B x).le_opNorm y
      _ ≤ ‖B‖ * ‖x‖ * ‖y‖ * ‖z‖ * ‖u‖ := by
        gcongr
        exact B.le_opNorm x

  have termBound (a b : ForcingJet A T) (v w : ForcingJet V T)
      (x y : A) (z u : V)
      (hx : ‖x‖ ≤ ‖a‖) (hy : ‖y‖ ≤ ‖b‖)
      (hz : ‖z‖ ≤ ‖v‖) (hu : ‖u‖ ≤ ‖w‖) :
      ‖B x y z u‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖ := by
    calc
      ‖B x y z u‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ * ‖z‖ * ‖u‖ := Bbound x y z u
      _ ≤ ‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖ := by gcongr

  have firstRawBound (a b : ForcingJet A T) (v w : ForcingJet V T)
      (p : Slab T) :
      ‖firstRaw a b v w p‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖ := by
    exact termBound a b v w (a.1 p) (b.1 p) (v.1 p) (w.1 p)
      (jetFirstBoundA a p) (jetFirstBoundA b p) (jetFirstBoundV v p)
      (jetFirstBoundV w p)

  have secondRawBound (a b : ForcingJet A T) (v w : ForcingJet V T)
      (p : Pair T) :
      ‖secondRaw a b v w p‖ ≤
        4 * (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖) := by
    let x₀ := a.1 p.1.1
    let x₁ := a.1 p.1.2
    let y₀ := b.1 p.1.1
    let y₁ := b.1 p.1.2
    let z₀ := v.1 p.1.1
    let z₁ := v.1 p.1.2
    let u₀ := w.1 p.1.1
    let u₁ := w.1 p.1.2
    have h₁ := termBound a b v w (a.2 p) y₀ z₀ u₀
      (jetSecondBoundA a p) (jetFirstBoundA b p.1.1)
      (jetFirstBoundV v p.1.1) (jetFirstBoundV w p.1.1)
    have h₂ := termBound a b v w x₁ (b.2 p) z₀ u₀
      (jetFirstBoundA a p.1.2) (jetSecondBoundA b p)
      (jetFirstBoundV v p.1.1) (jetFirstBoundV w p.1.1)
    have h₃ := termBound a b v w x₁ y₁ (v.2 p) u₀
      (jetFirstBoundA a p.1.2) (jetFirstBoundA b p.1.2)
      (jetSecondBoundV v p) (jetFirstBoundV w p.1.1)
    have h₄ := termBound a b v w x₁ y₁ z₁ (w.2 p)
      (jetFirstBoundA a p.1.2) (jetFirstBoundA b p.1.2)
      (jetFirstBoundV v p.1.2) (jetSecondBoundV w p)
    let t₁ := B (a.2 p) y₀ z₀ u₀
    let t₂ := B x₁ (b.2 p) z₀ u₀
    let t₃ := B x₁ y₁ (v.2 p) u₀
    let t₄ := B x₁ y₁ z₁ (w.2 p)
    have h123 : ‖t₁ + t₂ + t₃‖ ≤ ‖t₁‖ + ‖t₂‖ + ‖t₃‖ := by
      calc
        ‖t₁ + t₂ + t₃‖ ≤ ‖t₁ + t₂‖ + ‖t₃‖ := norm_add_le _ _
        _ ≤ (‖t₁‖ + ‖t₂‖) + ‖t₃‖ :=
          add_le_add_left (norm_add_le _ _) ‖t₃‖
    have hsum :
        ‖t₁ + t₂ + t₃ + t₄‖ ≤ ‖t₁‖ + ‖t₂‖ + ‖t₃‖ + ‖t₄‖ := by
      calc
        ‖t₁ + t₂ + t₃ + t₄‖ ≤ ‖t₁ + t₂ + t₃‖ + ‖t₄‖ := norm_add_le _ _
        _ ≤ (‖t₁‖ + ‖t₂‖ + ‖t₃‖) + ‖t₄‖ :=
          add_le_add_left h123 ‖t₄‖
    calc
      ‖secondRaw a b v w p‖ =
          ‖B (a.2 p) y₀ z₀ u₀ + B x₁ (b.2 p) z₀ u₀ +
            B x₁ y₁ (v.2 p) u₀ + B x₁ y₁ z₁ (w.2 p)‖ := by
              simp [secondRaw, x₁, y₀, y₁, z₀, z₁, u₀]
      _ ≤ _ := hsum
      _ ≤ (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖) +
          (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖) +
          (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖) +
          (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖) := by gcongr
      _ = 4 * (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖) := by ring

  let firstField (a b : ForcingJet A T) (v w : ForcingJet V T) : Slab T →ᵇ Z :=
    BoundedContinuousFunction.ofNormedAddCommGroup (firstRaw a b v w)
      (firstCont a b v w) (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖)
      (firstRawBound a b v w)
  let secondField (a b : ForcingJet A T) (v w : ForcingJet V T) : Pair T →ᵇ Z :=
    BoundedContinuousFunction.ofNormedAddCommGroup (secondRaw a b v w)
      (secondCont a b v w) (4 * (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖))
      (secondRawBound a b v w)
  let quad (a b : ForcingJet A T) (v w : ForcingJet V T) : ForcingJet Z T :=
    (firstField a b v w, secondField a b v w)

  have firstFieldNorm (a b : ForcingJet A T) (v w : ForcingJet V T) :
      ‖firstField a b v w‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖ := by
    change ‖BoundedContinuousFunction.ofNormedAddCommGroup (firstRaw a b v w)
      (firstCont a b v w) (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖)
      (firstRawBound a b v w)‖ ≤ _
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (firstCont a b v w) (by positivity) (firstRawBound a b v w)
  have secondFieldNorm (a b : ForcingJet A T) (v w : ForcingJet V T) :
      ‖secondField a b v w‖ ≤ 4 * (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖) := by
    change ‖BoundedContinuousFunction.ofNormedAddCommGroup (secondRaw a b v w)
      (secondCont a b v w) (4 * (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖))
      (secondRawBound a b v w)‖ ≤ _
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (secondCont a b v w) (by positivity) (secondRawBound a b v w)
  have quadNorm (a b : ForcingJet A T) (v w : ForcingJet V T) :
      ‖quad a b v w‖ ≤ 4 * (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖) := by
    change max ‖firstField a b v w‖ ‖secondField a b v w‖ ≤ _
    apply max_le
    · calc
        ‖firstField a b v w‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖ :=
          firstFieldNorm a b v w
        _ ≤ 4 * (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖) := by
          have hc : 0 ≤ ‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖ := by positivity
          nlinarith
    · exact secondFieldNorm a b v w

  have quad_add_a (a₁ a₂ b : ForcingJet A T) (v w : ForcingJet V T) :
      quad (a₁ + a₂) b v w = quad a₁ b v w + quad a₂ b v w := by
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro p
      change firstRaw (a₁ + a₂) b v w p =
        firstRaw a₁ b v w p + firstRaw a₂ b v w p
      simp [firstRaw, map_add]
    · apply BoundedContinuousFunction.ext
      intro p
      change secondRaw (a₁ + a₂) b v w p =
        secondRaw a₁ b v w p + secondRaw a₂ b v w p
      simp [secondRaw, map_add] <;> abel
  have quad_smul_a (c : ℝ) (a : ForcingJet A T) (b : ForcingJet A T)
      (v w : ForcingJet V T) : quad (c • a) b v w = c • quad a b v w := by
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro p
      change firstRaw (c • a) b v w p = c • firstRaw a b v w p
      simp [firstRaw, map_smul]
    · apply BoundedContinuousFunction.ext
      intro p
      change secondRaw (c • a) b v w p = c • secondRaw a b v w p
      simp [secondRaw, map_smul, smul_add]

  have quad_add_b (a : ForcingJet A T) (b₁ b₂ : ForcingJet A T)
      (v w : ForcingJet V T) :
      quad a (b₁ + b₂) v w = quad a b₁ v w + quad a b₂ v w := by
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro p
      change firstRaw a (b₁ + b₂) v w p =
        firstRaw a b₁ v w p + firstRaw a b₂ v w p
      simp [firstRaw, map_add]
    · apply BoundedContinuousFunction.ext
      intro p
      change secondRaw a (b₁ + b₂) v w p =
        secondRaw a b₁ v w p + secondRaw a b₂ v w p
      simp [secondRaw, map_add] <;> abel
  have quad_smul_b (c : ℝ) (a b : ForcingJet A T) (v w : ForcingJet V T) :
      quad a (c • b) v w = c • quad a b v w := by
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro p
      change firstRaw a (c • b) v w p = c • firstRaw a b v w p
      simp [firstRaw, map_smul]
    · apply BoundedContinuousFunction.ext
      intro p
      change secondRaw a (c • b) v w p = c • secondRaw a b v w p
      simp [secondRaw, map_smul, smul_add]

  have quad_add_v (a b : ForcingJet A T) (v₁ v₂ w : ForcingJet V T) :
      quad a b (v₁ + v₂) w = quad a b v₁ w + quad a b v₂ w := by
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro p
      change firstRaw a b (v₁ + v₂) w p =
        firstRaw a b v₁ w p + firstRaw a b v₂ w p
      simp [firstRaw, map_add]
    · apply BoundedContinuousFunction.ext
      intro p
      change secondRaw a b (v₁ + v₂) w p =
        secondRaw a b v₁ w p + secondRaw a b v₂ w p
      simp [secondRaw, map_add] <;> abel
  have quad_smul_v (c : ℝ) (a b : ForcingJet A T) (v w : ForcingJet V T) :
      quad a b (c • v) w = c • quad a b v w := by
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro p
      change firstRaw a b (c • v) w p = c • firstRaw a b v w p
      simp [firstRaw, map_smul]
    · apply BoundedContinuousFunction.ext
      intro p
      change secondRaw a b (c • v) w p = c • secondRaw a b v w p
      simp [secondRaw, map_smul, smul_add]

  have quad_add_w (a b : ForcingJet A T) (v w₁ w₂ : ForcingJet V T) :
      quad a b v (w₁ + w₂) = quad a b v w₁ + quad a b v w₂ := by
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro p
      change firstRaw a b v (w₁ + w₂) p =
        firstRaw a b v w₁ p + firstRaw a b v w₂ p
      simp [firstRaw, map_add]
    · apply BoundedContinuousFunction.ext
      intro p
      change secondRaw a b v (w₁ + w₂) p =
        secondRaw a b v w₁ p + secondRaw a b v w₂ p
      simp [secondRaw, map_add] <;> abel
  have quad_smul_w (c : ℝ) (a b : ForcingJet A T) (v w : ForcingJet V T) :
      quad a b v (c • w) = c • quad a b v w := by
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro p
      change firstRaw a b v (c • w) p = c • firstRaw a b v w p
      simp [firstRaw, map_smul]
    · apply BoundedContinuousFunction.ext
      intro p
      change secondRaw a b v (c • w) p = c • secondRaw a b v w p
      simp [secondRaw, map_smul, smul_add]

  let QwMap (a b : ForcingJet A T) (v : ForcingJet V T) :
      ForcingJet V T →ₗ[ℝ] ForcingJet Z T := {
    toFun := fun w => quad a b v w
    map_add' := quad_add_w a b v
    map_smul' := fun c w => quad_smul_w c a b v w
  }
  have QwPoint (a b : ForcingJet A T) (v w : ForcingJet V T) :
      ‖quad a b v w‖ ≤
        (4 * ‖B‖ * ‖a‖ * ‖b‖ * ‖v‖) * ‖w‖ := by
    calc
      ‖quad a b v w‖ ≤ 4 * (‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ * ‖w‖) :=
        quadNorm a b v w
      _ = (4 * ‖B‖ * ‖a‖ * ‖b‖ * ‖v‖) * ‖w‖ := by ring
  let Qw (a b : ForcingJet A T) (v : ForcingJet V T) :
      ForcingJet V T →L[ℝ] ForcingJet Z T :=
    (QwMap a b v).mkContinuous (4 * ‖B‖ * ‖a‖ * ‖b‖ * ‖v‖)
      (QwPoint a b v)
  have QwNorm (a b : ForcingJet A T) (v : ForcingJet V T) :
      ‖Qw a b v‖ ≤ 4 * ‖B‖ * ‖a‖ * ‖b‖ * ‖v‖ := by
    exact LinearMap.mkContinuous_norm_le (QwMap a b v) (by positivity)
      (QwPoint a b v)

  let QvMap (a b : ForcingJet A T) :
      ForcingJet V T →ₗ[ℝ] (ForcingJet V T →L[ℝ] ForcingJet Z T) := {
    toFun := Qw a b
    map_add' := by
      intro v₁ v₂
      apply ContinuousLinearMap.ext
      intro w
      simpa [Qw, QwMap] using quad_add_v a b v₁ v₂ w
    map_smul' := by
      intro c v
      apply ContinuousLinearMap.ext
      intro w
      simpa [Qw, QwMap] using quad_smul_v c a b v w
  }
  have QvPoint (a b : ForcingJet A T) (v : ForcingJet V T) :
      ‖Qw a b v‖ ≤ (4 * ‖B‖ * ‖a‖ * ‖b‖) * ‖v‖ := by
    simpa [mul_assoc] using QwNorm a b v
  let Qv (a b : ForcingJet A T) :
      ForcingJet V T →L[ℝ] (ForcingJet V T →L[ℝ] ForcingJet Z T) :=
    (QvMap a b).mkContinuous (4 * ‖B‖ * ‖a‖ * ‖b‖) (QvPoint a b)
  have QvNorm (a b : ForcingJet A T) :
      ‖Qv a b‖ ≤ 4 * ‖B‖ * ‖a‖ * ‖b‖ := by
    exact LinearMap.mkContinuous_norm_le (QvMap a b) (by positivity)
      (QvPoint a b)

  let QbMap (a : ForcingJet A T) :
      ForcingJet A T →ₗ[ℝ]
        (ForcingJet V T →L[ℝ] (ForcingJet V T →L[ℝ] ForcingJet Z T)) := {
    toFun := Qv a
    map_add' := by
      intro b₁ b₂
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      simpa [Qv, QvMap, Qw, QwMap] using quad_add_b a b₁ b₂ v w
    map_smul' := by
      intro c b
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      simpa [Qv, QvMap, Qw, QwMap] using quad_smul_b c a b v w
  }
  have QbPoint (a : ForcingJet A T) (b : ForcingJet A T) :
      ‖Qv a b‖ ≤ (4 * ‖B‖ * ‖a‖) * ‖b‖ := by
    simpa [mul_assoc] using QvNorm a b
  let Qb (a : ForcingJet A T) :
      ForcingJet A T →L[ℝ]
        (ForcingJet V T →L[ℝ] (ForcingJet V T →L[ℝ] ForcingJet Z T)) :=
    (QbMap a).mkContinuous (4 * ‖B‖ * ‖a‖) (QbPoint a)
  have QbNorm (a : ForcingJet A T) :
      ‖Qb a‖ ≤ 4 * ‖B‖ * ‖a‖ := by
    exact LinearMap.mkContinuous_norm_le (QbMap a) (by positivity)
      (QbPoint a)

  let QaMap :
      ForcingJet A T →ₗ[ℝ]
        (ForcingJet A T →L[ℝ]
          (ForcingJet V T →L[ℝ] (ForcingJet V T →L[ℝ] ForcingJet Z T))) := {
    toFun := Qb
    map_add' := by
      intro a₁ a₂
      apply ContinuousLinearMap.ext
      intro b
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      simpa [Qb, QbMap, Qv, QvMap, Qw, QwMap] using quad_add_a a₁ a₂ b v w
    map_smul' := by
      intro c a
      apply ContinuousLinearMap.ext
      intro b
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      simpa [Qb, QbMap, Qv, QvMap, Qw, QwMap] using quad_smul_a c a b v w
  }
  have QaPoint (a : ForcingJet A T) :
      ‖Qb a‖ ≤ (4 * ‖B‖) * ‖a‖ := by
    simpa [mul_assoc] using QbNorm a
  let Q : ForcingJet A T →L[ℝ] ForcingJet A T →L[ℝ]
      ForcingJet V T →L[ℝ] ForcingJet V T →L[ℝ] ForcingJet Z T :=
    QaMap.mkContinuous (4 * ‖B‖) QaPoint

  have Qnorm : ‖Q‖ ≤ 4 * ‖B‖ :=
    LinearMap.mkContinuous_norm_le QaMap (by positivity) QaPoint
  have Qapply (a b : ForcingJet A T) (v w : ForcingJet V T) :
      Q a b v w = quad a b v w := by
    rfl

  refine ⟨Q, ?_, ?_, ?_⟩
  · calc
      ‖Q‖ ≤ 4 * ‖B‖ := Qnorm
      _ ≤ 8 * ‖B‖ := by nlinarith [norm_nonneg B]
  · intro a b v w p
    rw [Qapply]
    change firstRaw a b v w p = B (a.1 p) (b.1 p) (v.1 p) (w.1 p)
    rfl
  · intro a ha b hb v hv w hw p
    let r : ℝ := (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹
    let x₀ : A := a.1 p.1.1
    let x₁ : A := a.1 p.1.2
    let y₀ : A := b.1 p.1.1
    let y₁ : A := b.1 p.1.2
    let z₀ : V := v.1 p.1.1
    let z₁ : V := v.1 p.1.2
    let u₀ : V := w.1 p.1.1
    let u₁ : V := w.1 p.1.2
    have ha' : a.2 p = r • (x₀ - x₁) := by
      simpa [r, x₀, x₁] using ha p
    have hb' : b.2 p = r • (y₀ - y₁) := by
      simpa [r, y₀, y₁] using hb p
    have hv' : v.2 p = r • (z₀ - z₁) := by
      simpa [r, z₀, z₁] using hv p
    have hw' : w.2 p = r • (u₀ - u₁) := by
      simpa [r, u₀, u₁] using hw p
    have hsplit :
        B x₀ y₀ z₀ u₀ - B x₁ y₁ z₁ u₁ =
          B (x₀ - x₁) y₀ z₀ u₀ + B x₁ (y₀ - y₁) z₀ u₀ +
          B x₁ y₁ (z₀ - z₁) u₀ + B x₁ y₁ z₁ (u₀ - u₁) := by
      have h₁ : B (x₀ - x₁) y₀ z₀ u₀ =
          B x₀ y₀ z₀ u₀ - B x₁ y₀ z₀ u₀ := by
        rw [map_sub]
        simp
      have h₂ : B x₁ (y₀ - y₁) z₀ u₀ =
          B x₁ y₀ z₀ u₀ - B x₁ y₁ z₀ u₀ := by
        rw [map_sub]
        simp
      have h₃ : B x₁ y₁ (z₀ - z₁) u₀ =
          B x₁ y₁ z₀ u₀ - B x₁ y₁ z₁ u₀ := by
        rw [map_sub]
        simp
      have h₄ : B x₁ y₁ z₁ (u₀ - u₁) =
          B x₁ y₁ z₁ u₀ - B x₁ y₁ z₁ u₁ := by
        rw [map_sub]
      calc
        B x₀ y₀ z₀ u₀ - B x₁ y₁ z₁ u₁ =
            (B x₀ y₀ z₀ u₀ - B x₁ y₀ z₀ u₀) +
              (B x₁ y₀ z₀ u₀ - B x₁ y₁ z₀ u₀) +
              (B x₁ y₁ z₀ u₀ - B x₁ y₁ z₁ u₀) +
              (B x₁ y₁ z₁ u₀ - B x₁ y₁ z₁ u₁) := by abel
        _ = _ := by rw [← h₁, ← h₂, ← h₃, ← h₄]
    rw [Qapply]
    change secondRaw a b v w p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (firstRaw a b v w p.1.1 - firstRaw a b v w p.1.2)
    change
      B (a.2 p) (b.1 p.1.1) (v.1 p.1.1) (w.1 p.1.1) +
        B (a.1 p.1.2) (b.2 p) (v.1 p.1.1) (w.1 p.1.1) +
        B (a.1 p.1.2) (b.1 p.1.2) (v.2 p) (w.1 p.1.1) +
        B (a.1 p.1.2) (b.1 p.1.2) (v.1 p.1.2) (w.2 p) =
      r • (B (a.1 p.1.1) (b.1 p.1.1) (v.1 p.1.1) (w.1 p.1.1) -
        B (a.1 p.1.2) (b.1 p.1.2) (v.1 p.1.2) (w.1 p.1.2))
    rw [ha', hb', hv', hw']
    calc
      B (r • (x₀ - x₁)) y₀ z₀ u₀ +
          B x₁ (r • (y₀ - y₁)) z₀ u₀ +
          B x₁ y₁ (r • (z₀ - z₁)) u₀ +
          B x₁ y₁ z₁ (r • (u₀ - u₁)) =
        r • (B (x₀ - x₁) y₀ z₀ u₀ + B x₁ (y₀ - y₁) z₀ u₀ +
          B x₁ y₁ (z₀ - z₁) u₀ + B x₁ y₁ z₁ (u₀ - u₁)) := by
            simp only [map_smul, smul_apply, smul_add]
      _ = r • (B x₀ y₀ z₀ u₀ - B x₁ y₁ z₁ u₁) := by rw [hsplit]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingGraphQuadrilinearLift
