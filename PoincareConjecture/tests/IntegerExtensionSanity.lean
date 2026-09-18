import PoincareConjecture

open Set Bundle Manifold Function
open PoincareConjecture.Topology.FiberSaturation
open SmoothBundle
open scoped Manifold ContDiff
noncomputable section

-- The period convention is floor, not truncation toward zero.
example : periodIndex 4 (-1) = -1 := by norm_num [periodIndex]
example : periodRemainder 4 (-1) = 3 := by norm_num [periodRemainder,periodIndex]
example : periodIndex 4 (-4) = -1 := by norm_num [periodIndex]
example : periodRemainder 4 (-4) = 0 := by norm_num [periodRemainder,periodIndex]

def extensionDeck : (ℝ × ℝ) ≃ₘ⟮(𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ),
    (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)⟯ (ℝ × ℝ) :=
  (realTranslation 4).prodCongr (realTranslation (-1))
def extensionTwist : ℝ ≃ₘ⟮𝓘(ℝ,ℝ),𝓘(ℝ,ℝ)⟯ ℝ := realTranslation 1

theorem extension_seam (t x : ℝ) :
    (t+4,x) = extensionDeck (t,extensionTwist x) := by
  change (t+4,x) = (t+4,x+1+(-1))
  simp

-- Both sides of a seam are handled, not merely open period interiors.
example : IsLocalDiffeomorph ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ))
    ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)) ∞
    (periodicExtend extensionDeck.toHomeomorph extensionTwist.toHomeomorph id 4) := by
  apply periodicExtend_isLocalDiffeomorph extensionDeck extensionTwist id
    (ε := 1) (by norm_num) (by norm_num) (by norm_num)
  · intro t x _
    exact extension_seam t x
  · intro t _ x
    exact (Diffeomorph.refl _ (ℝ × ℝ) ∞).isLocalDiffeomorph (t,x)

-- The twist is not an involution; its orientation matters at negative periods.
example (x : ℝ) : periodicExtend extensionDeck.toHomeomorph extensionTwist.toHomeomorph id 4
    (-4,x) = (-4,x) := by
  norm_num [periodicExtend,periodIndex,periodRemainder,extensionDeck,extensionTwist,
    Homeomorph.inv_apply,realTranslation,Diffeomorph.prodCongr]
  change ((0 : ℝ)-4,(x-1)-(-1)) = (-4,x)
  ext <;> ring

example (x : ℝ) : periodicExtend extensionDeck.toHomeomorph extensionTwist.toHomeomorph id 4
    (4,x) = (4,x) := by
  norm_num [periodicExtend,periodIndex,periodRemainder,extensionDeck,extensionTwist,
    realTranslation,Diffeomorph.prodCongr]
  change ((0 : ℝ)+4,(x+1)+(-1)) = (4,x)
  ext <;> ring

/-- Actual product chart, to be restricted to proper open base sets below. -/
def extensionProductChart (F : Type*) [TopologicalSpace F] :
    Trivialization F (Prod.fst : ℝ × F → ℝ) where
  toOpenPartialHomeomorph := (Homeomorph.refl (ℝ × F)).toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := by simp
  proj_toFun _ _ := rfl

def extensionShear : (ℝ × ℝ) ≃ₘ⟮(𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ),
    (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)⟯ (ℝ × ℝ) where
  toFun z := (z.1,z.2+z.1)
  invFun z := (z.1,z.2-z.1)
  left_inv _ := by simp
  right_inv _ := by simp
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_fst)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_fst)

def extensionVariableDeck : (ℝ × ℝ) ≃ₘ⟮(𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ),
    (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)⟯ (ℝ × ℝ) where
  toFun z := (z.1+4,z.2+z.1)
  invFun z := (z.1-4,z.2-(z.1-4))
  left_inv _ := by simp
  right_inv _ := by simp
  contMDiff_toFun := (contMDiff_fst.add contMDiff_const).prodMk
    (contMDiff_snd.add contMDiff_fst)
  contMDiff_invFun := (contMDiff_fst.sub contMDiff_const).prodMk
    (contMDiff_snd.sub (contMDiff_fst.sub contMDiff_const))

-- Neither supplied chart covers [0,4], and the deck map changes the fiber with time.
example : ∃ φ : ℝ ≃ₘ⟮𝓘(ℝ,ℝ),𝓘(ℝ,ℝ)⟯ ℝ,
    ∃ e : (ℝ × ℝ) ≃ₘ⟮(𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ),(𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)⟯ (ℝ × ℝ),
      (∀ t x, (e (t,x)).1 = t) ∧
      (∀ n : ℤ, ∀ t x, e (t+(n : ℝ)*4,x) =
        (extensionVariableDeck.toHomeomorph ^ n) (e (t,(φ.toHomeomorph ^ n) x))) := by
  have he : IsSmoothTrivialization ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ)
      (extensionProductChart ℝ) := ⟨contMDiff_id.contMDiffOn,contMDiff_id.contMDiffOn⟩
  have hf := isSmooth_adjust he extensionShear (fun _ => rfl)
  apply exists_equivariant_real_diffeomorph continuous_fst ?_ extensionVariableDeck
    (by norm_num) (fun _ => rfl)
  intro t
  by_cases ht : t < 3
  · exact ⟨(extensionProductChart ℝ).restrOpen (Iio 3) isOpen_Iio,
      ⟨mem_univ _,ht⟩,isSmooth_restrOpen he _ _⟩
  · refine ⟨(adjust (extensionProductChart ℝ) extensionShear (fun _ => rfl)).restrOpen
      (Ioi 1) isOpen_Ioi,⟨mem_univ _,?_⟩,isSmooth_restrOpen hf _ _⟩
    change (1 : ℝ) < t
    linarith

-- Actual sphere with its existing smooth structure, not an abstract connected type.
example : ∃ _φ : Sphere2 ≃ₘ⟮𝓡 2,𝓡 2⟯ Sphere2,
    ∃ e : (ℝ × Sphere2) ≃ₘ⟮(𝓘(ℝ,ℝ)).prod (𝓡 2),(𝓘(ℝ,ℝ)).prod (𝓡 2)⟯ (ℝ × Sphere2),
      ∀ t x, (e (t,x)).1 = t := by
  have hloc : ∀ t : ℝ, ∃ k : Trivialization Sphere2 (Prod.fst : ℝ × Sphere2 → ℝ),
      t ∈ k.baseSet ∧ IsSmoothTrivialization ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 2) k := by
    intro t
    exact ⟨extensionProductChart Sphere2,mem_univ _,
      contMDiff_id.contMDiffOn,contMDiff_id.contMDiffOn⟩
  obtain ⟨φ,e,he,_⟩ := exists_equivariant_real_diffeomorph continuous_fst hloc
    ((realTranslation 4).prodCongr (Diffeomorph.refl (𝓡 2) Sphere2 ∞))
    (by norm_num : (0 : ℝ) < 4) (fun _ => rfl)
  exact ⟨φ,e,he⟩
