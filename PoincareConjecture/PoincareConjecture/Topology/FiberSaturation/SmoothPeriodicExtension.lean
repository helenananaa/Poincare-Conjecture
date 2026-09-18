import PoincareConjecture.Topology.FiberSaturation.SmoothIntegerPowers
import PoincareConjecture.Topology.FiberSaturation.PeriodicExtension

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Function Manifold Filter
open scoped Manifold ContDiff Topology
variable {V W H G M F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace F] [ChartedSpace G F]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G}

/-- Local invertibility and smoothness depend only on the germ of the map. -/
theorem localDiffeomorphAt_of_eventuallyEq {f g : F → M} {x : F}
    (hg : IsLocalDiffeomorphAt J I ∞ g x) (hfg : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt J I ∞ f x := by
  obtain ⟨Φ,hx,heq⟩ := hg
  obtain ⟨s,hs,hso,hxs⟩ := mem_nhds_iff.mp hfg
  let r := Φ.toOpenPartialHomeomorph.restrOpen s hso
  refine ⟨{ toPartialEquiv := r.toPartialEquiv
            open_source := r.open_source
            open_target := r.open_target
            contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
            contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left },
    ⟨hx,hxs⟩, fun y hy => (hs hy.2).trans (heq hy.1)⟩

/-- A fixed cell is a composition of smooth integer iterates and translations. -/
theorem periodicCell_localDiffeomorphAt (T : M ≃ₘ⟮I,I⟯ M) (φ : F ≃ₘ⟮J,J⟯ F)
    (P : ℝ × F → M) (L : ℝ) (n : ℤ) (t : ℝ) (x : F)
    (hP : IsLocalDiffeomorphAt ((𝓘(ℝ,ℝ)).prod J) I ∞ P
      (t-(n : ℝ)*L,(φ.toHomeomorph ^ n) x)) :
    IsLocalDiffeomorphAt ((𝓘(ℝ,ℝ)).prod J) I ∞
      (periodicCell T.toHomeomorph φ.toHomeomorph P L n) (t,x) := by
  let C := (realTranslation (-((n : ℝ)*L))).prodCongr (integerDiffeomorph φ n)
  have hC (s : ℝ) (y : F) : C (s,y) = (s-(n : ℝ)*L,(φ.toHomeomorph ^ n) y) := by
    apply Prod.ext
    · change s + -((n : ℝ)*L) = s-(n : ℝ)*L
      ring
    · rfl
  have heq : periodicCell T.toHomeomorph φ.toHomeomorph P L n =
      (integerDiffeomorph T n) ∘ P ∘ C := by
    funext z
    rcases z with ⟨s,y⟩
    simp only [Function.comp_apply,hC]
    rfl
  rw [heq]
  have hP' : IsLocalDiffeomorphAt ((𝓘(ℝ,ℝ)).prod J) I ∞ P (C (t,x)) := by
    rw [hC]
    exact hP
  exact ((C.isLocalDiffeomorph (t,x)).comp I M hP').comp I M
    ((integerDiffeomorph T n).isLocalDiffeomorph _)

/-- The extension is a local diffeomorphism at every real time, including all
integer seams. The discontinuous period index is never differentiated. -/
theorem periodicExtend_isLocalDiffeomorph (T : M ≃ₘ⟮I,I⟯ M) (φ : F ≃ₘ⟮J,J⟯ F)
    (P : ℝ × F → M) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (hεL : ε < L)
    (hseam : ∀ t x, t ∈ Ioo (-ε) ε → P (t+L,x) = T (P (t,φ x)))
    (hP : ∀ t ∈ Ioo (-ε) (L+ε), ∀ x,
      IsLocalDiffeomorphAt ((𝓘(ℝ,ℝ)).prod J) I ∞ P (t,x)) :
    IsLocalDiffeomorph ((𝓘(ℝ,ℝ)).prod J) I ∞
      (periodicExtend T.toHomeomorph φ.toHomeomorph P L) := by
  rintro ⟨t,x⟩
  let n := periodIndex L t
  have hr := periodRemainder_mem hL t
  have ht : t-(n : ℝ)*L ∈ Ioo (-ε) (L+ε) := by
    change 0 ≤ t-(n : ℝ)*L ∧ t-(n : ℝ)*L < L at hr
    constructor <;> linarith [hr.1,hr.2]
  apply localDiffeomorphAt_of_eventuallyEq
    (periodicCell_localDiffeomorphAt T φ P L n t x (hP _ ht _))
  have hopen : IsOpen {z : ℝ × F | z.1-(n : ℝ)*L ∈ Ioo (-ε) (L+ε)} :=
    isOpen_Ioo.preimage (continuous_fst.sub continuous_const)
  filter_upwards [hopen.mem_nhds ht] with z hz
  exact periodicExtend_eq_cell T.toHomeomorph φ.toHomeomorph P hL hε hεL hseam n hz z.2

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
