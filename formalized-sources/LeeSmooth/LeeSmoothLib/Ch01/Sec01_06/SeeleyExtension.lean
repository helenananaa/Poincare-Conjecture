import Mathlib

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace LeeSmooth.SeeleyExtension

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma polynomial_coeff_finset_sum {R ι : Type*} [Semiring R]
    (s : Finset ι) (p : ι → Polynomial R) (m : ℕ) :
    (∑ i ∈ s, p i).coeff m = ∑ i ∈ s, (p i).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

/-- Scalar multiplication of an entire Taylor field. -/
lemma HasFTaylorSeriesUpToOn.const_smul_real
    {r : ℕ∞ω} {s : Set E} {f : E → F}
    {p : E → FormalMultilinearSeries ℝ E F}
    (hp : HasFTaylorSeriesUpToOn r f p s) (c : ℝ) :
    HasFTaylorSeriesUpToOn r (fun x ↦ c • f x) (fun x m ↦ c • p x m) s := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change c • (p x 0).curry0 = c • f x
    rw [hp.zero_eq x hx]
  · intro m hm x hx
    change HasFDerivWithinAt (fun y ↦ c • p y m) ((c • p x (m + 1)).curryLeft) s x
    rw [show (fun y ↦ c • p y m) = c • (p · m) by rfl]
    rw [show (c • p x (m + 1)).curryLeft = c • (p x (m + 1)).curryLeft by
      ext y
      rfl]
    exact (hp.fderivWithin m hm x hx).const_smul c
  · intro m hm
    change ContinuousOn (c • (p · m)) s
    exact (hp.cont m hm).const_smul c

/-- A finite linear combination of Taylor fields is again a Taylor field, with the
same finite linear combination in every order. -/
lemma HasFTaylorSeriesUpToOn.finset_sum_const_smul
    {r : ℕ∞ω} {s : Set E} {ι : Type*} (I : Finset ι)
    (a : ι → ℝ) (f : ι → E → F)
    (p : ι → E → FormalMultilinearSeries ℝ E F)
    (hp : ∀ i ∈ I, HasFTaylorSeriesUpToOn r (f i) (p i) s) :
    HasFTaylorSeriesUpToOn r
      (fun x ↦ ∑ i ∈ I, a i • f i x)
      (fun x m ↦ ∑ i ∈ I, a i • p i x m) s := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨?_, ?_, ?_⟩
      · simp
      · intro m hm x hx
        simp only [Finset.sum_empty]
        have h : HasFDerivWithinAt
            (fun _ : E ↦ (0 : E [×m]→L[ℝ] F))
            (0 : E →L[ℝ] (E [×m]→L[ℝ] F)) s x :=
          hasFDerivWithinAt_const (c := (0 : E [×m]→L[ℝ] F)) x s
        convert h using 1
        ext y v
        rfl
      · intro m hm
        exact continuousOn_const
  | @insert i I hi hI =>
      simp only [Finset.sum_insert hi]
      exact HasFTaylorSeriesUpToOn.add
        (HasFTaylorSeriesUpToOn.const_smul_real
          (hp i (Finset.mem_insert_self i I)) (a i))
        (hI fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))

/-! ## Finite reflection coefficients -/

/-- The negative interpolation nodes used in the order-`r` reflection formula. -/
def finiteReflectionNode (r : ℕ) (j : Fin (r + 1)) : ℝ := -((j : ℕ) + 1 : ℝ)

/-- Lagrange's coefficient for evaluating a degree-at-most-`r` polynomial at `1`
from its values at the negative nodes `-1, ..., -(r+1)`. -/
def finiteReflectionCoeff (r : ℕ) (j : Fin (r + 1)) : ℝ :=
  (Lagrange.basis Finset.univ (finiteReflectionNode r) j).eval 1

lemma finiteReflectionNode_injective (r : ℕ) : Function.Injective (finiteReflectionNode r) := by
  intro i j hij
  apply Fin.ext
  have hij' : (i : ℝ) = (j : ℝ) := by
    simp only [finiteReflectionNode, neg_inj] at hij
    linarith
  exact_mod_cast hij'

/-- The finite reflection coefficients match every normal derivative through order `r`. -/
lemma sum_finiteReflectionCoeff_mul_node_pow (r m : ℕ) (hm : m ≤ r) :
    ∑ j : Fin (r + 1), finiteReflectionCoeff r j * finiteReflectionNode r j ^ m = 1 := by
  let P : Polynomial ℝ := Polynomial.X ^ m
  have hdeg : P.degree < (Finset.univ : Finset (Fin (r + 1))).card := by
    rw [show (Finset.univ : Finset (Fin (r + 1))).card = r + 1 by simp]
    simp only [P, Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_iff.mpr hm
  have hinterp := Lagrange.eq_interpolate
    (s := (Finset.univ : Finset (Fin (r + 1))))
    (v := finiteReflectionNode r) (f := P)
    (finiteReflectionNode_injective r).injOn hdeg
  have heval := congrArg (Polynomial.eval (1 : ℝ)) hinterp
  symm
  simpa [P, finiteReflectionCoeff, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum, mul_comm] using heval

/-- Coefficients of a moment-correction block.  Unlike `finiteReflectionCoeff`, which
evaluates an interpolated polynomial at `1`, these read off its top coefficient. -/
def momentCorrectionCoeff (r : ℕ) (j : Fin (r + 1)) : ℝ :=
  (Lagrange.basis Finset.univ (finiteReflectionNode r) j).coeff r

/-- The order-`r` correction block kills every lower moment and has `r`-th moment one.
This is the algebraic triangularity needed by a recursive infinite Seeley construction. -/
lemma sum_momentCorrectionCoeff_mul_node_pow (r q : ℕ) (hq : q ≤ r) :
    ∑ j : Fin (r + 1), momentCorrectionCoeff r j * finiteReflectionNode r j ^ q =
      if q = r then 1 else 0 := by
  let P : Polynomial ℝ := Polynomial.X ^ q
  have hdeg : P.degree < (Finset.univ : Finset (Fin (r + 1))).card := by
    rw [show (Finset.univ : Finset (Fin (r + 1))).card = r + 1 by simp]
    simp only [P, Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_iff.mpr hq
  have hinterp := Lagrange.eq_interpolate
    (s := (Finset.univ : Finset (Fin (r + 1))))
    (v := finiteReflectionNode r) (f := P)
    (finiteReflectionNode_injective r).injOn hdeg
  calc
    ∑ j : Fin (r + 1), momentCorrectionCoeff r j * finiteReflectionNode r j ^ q =
        (Lagrange.interpolate Finset.univ (finiteReflectionNode r)
          (fun j ↦ P.eval (finiteReflectionNode r j))).coeff r := by
      simp only [Lagrange.interpolate_apply]
      rw [polynomial_coeff_finset_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [P, momentCorrectionCoeff, Polynomial.eval_pow, Polynomial.eval_X]
      rw [Polynomial.coeff_C_mul, mul_comm]
    _ = P.coeff r := congrArg (fun Q : Polynomial ℝ ↦ Q.coeff r) hinterp.symm
    _ = if q = r then 1 else 0 := by
      simp [P, Polynomial.coeff_X_pow, eq_comm]

/-- Multilinearity converts scalar moment identities into equality of all jets.
This isolates the algebraic heart of finite reflection from the analytic gluing argument. -/
lemma weighted_multilinear_add_eq
    {ι : Type*} [Fintype ι] (m : ℕ) (a c : ι → ℝ)
    (hmom : ∀ q : ℕ, q ≤ m → ∑ j, a j * c j ^ q = 1)
    (M : E [×m]→L[ℝ] F) (u v : Fin m → E) :
    (∑ j, a j • M (fun i ↦ c j • u i + v i)) = M (fun i ↦ u i + v i) := by
  classical
  change (∑ j, a j • M ((fun i ↦ c j • u i) + v)) = M (u + v)
  rw [M.map_add_univ u v]
  simp_rw [M.map_add_univ (fun i ↦ c _ • u i) v]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hterm : ∀ j : ι,
      M (s.piecewise (fun i ↦ c j • u i) v) =
        c j ^ s.card • M (s.piecewise u v) := by
    intro j
    have harg :
        s.piecewise (fun i ↦ c j • u i) v =
          s.piecewise (fun i ↦ c j • (s.piecewise u v) i) (s.piecewise u v) := by
      funext i
      by_cases hi : i ∈ s <;> simp [hi]
    rw [harg]
    simpa [Finset.prod_const] using
      M.map_piecewise_smul (fun _ : Fin m ↦ c j) (s.piecewise u v) s
  simp_rw [hterm, smul_smul]
  rw [← Finset.sum_smul]
  have hcard : s.card ≤ m := by simpa using Finset.card_le_univ s
  rw [hmom s.card hcard, one_smul]

/-- The Lagrange reflection weights reproduce an arbitrary `m`-linear map after
simultaneously scaling the selected normal component in all inputs. -/
lemma finiteReflection_weighted_multilinear (r m : ℕ) (hm : m ≤ r)
    (M : E [×m]→L[ℝ] F) (u v : Fin m → E) :
    (∑ j : Fin (r + 1), finiteReflectionCoeff r j •
      M (fun i ↦ finiteReflectionNode r j • u i + v i)) =
      M (fun i ↦ u i + v i) := by
  exact weighted_multilinear_add_eq m (finiteReflectionCoeff r) (finiteReflectionNode r)
    (fun q hq ↦ sum_finiteReflectionCoeff_mul_node_pow r q (hq.trans hm)) M u v

/-! ## Euclidean normal reflection maps -/

variable {n : ℕ} [NeZero n]

/-- Projection onto the distinguished normal coordinate of the standard half-space. -/
def normalProjection :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.proj (i := (0 : Fin n))).smulRight (EuclideanSpace.single 0 1)

/-- Projection onto the coordinate hyperplane forming the boundary. -/
def tangentialProjection :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.id ℝ _ - normalProjection

/-- The linear map fixing tangential coordinates and multiplying the normal coordinate
by the `j`-th negative Lagrange node. -/
def finiteReflectionMap (r : ℕ) (j : Fin (r + 1)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  finiteReflectionNode r j • normalProjection + tangentialProjection

@[simp] lemma normalProjection_apply (z : EuclideanSpace ℝ (Fin n)) :
    normalProjection z = z 0 • EuclideanSpace.single 0 1 := rfl

lemma normal_add_tangential (z : EuclideanSpace ℝ (Fin n)) :
    normalProjection z + tangentialProjection z = z := by
  simp [tangentialProjection]

lemma finiteReflectionMap_apply (r : ℕ) (j : Fin (r + 1))
    (z : EuclideanSpace ℝ (Fin n)) :
    finiteReflectionMap r j z =
      finiteReflectionNode r j • normalProjection z + tangentialProjection z := by
  rfl

@[simp] lemma finiteReflectionMap_apply_zero (r : ℕ) (j : Fin (r + 1))
    (z : EuclideanSpace ℝ (Fin n)) :
    finiteReflectionMap r j z 0 = finiteReflectionNode r j * z 0 := by
  simp [finiteReflectionMap, tangentialProjection, normalProjection,
    EuclideanSpace.single_apply]

lemma finiteReflectionMap_of_normal_eq_zero (r : ℕ) (j : Fin (r + 1))
    {z : EuclideanSpace ℝ (Fin n)} (hz : z 0 = 0) : finiteReflectionMap r j z = z := by
  rw [finiteReflectionMap_apply]
  simp [normalProjection_apply, hz, tangentialProjection]

/-- At a boundary point, the transformed finite Taylor fields have the weighted
jet identity required for gluing through order `r`. -/
lemma finiteReflection_taylor_jet_eq (r m : ℕ) (hm : m ≤ r)
    (p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z 0 = 0) :
    (∑ j : Fin (r + 1), finiteReflectionCoeff r j •
      (p (finiteReflectionMap r j z) m).compContinuousLinearMap
        (fun _ ↦ finiteReflectionMap r j)) = p z m := by
  apply ContinuousMultilinearMap.ext
  intro w
  simp_rw [ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    finiteReflectionMap_of_normal_eq_zero r _ hz,
    finiteReflectionMap_apply]
  convert finiteReflection_weighted_multilinear r m hm (p z m)
    (fun i ↦ normalProjection (w i)) (fun i ↦ tangentialProjection (w i)) using 1
  exact congrArg (p z m) (funext fun i ↦ (normal_add_tangential (w i)).symm)

/-- The common domain on which every reflected evaluation lands in `S`. -/
def finiteReflectionDomain (r : ℕ) (S : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  ⋂ j : Fin (r + 1), finiteReflectionMap r j ⁻¹' S

/-- The order-`r` finite reflection formula on the negative side. -/
def finiteReflectionExtension (r : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → F) : EuclideanSpace ℝ (Fin n) → F :=
  fun z ↦ ∑ j : Fin (r + 1), finiteReflectionCoeff r j • f (finiteReflectionMap r j z)

/-- The Taylor field carried by the finite reflection formula. -/
def finiteReflectionTaylor (r : ℕ)
    (p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F) :
    EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F :=
  fun z m ↦ ∑ j : Fin (r + 1), finiteReflectionCoeff r j •
    (p (finiteReflectionMap r j z) m).compContinuousLinearMap
      (fun _ ↦ finiteReflectionMap r j)

lemma isClosed_finiteReflectionDomain (r : ℕ) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : IsClosed S) : IsClosed (finiteReflectionDomain r S) := by
  apply isClosed_iInter
  intro j
  exact hS.preimage (finiteReflectionMap r j).continuous

lemma finiteReflection_hasFTaylorSeriesUpToOn
    (r : ℕ) {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → F}
    {p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F}
    (hp : HasFTaylorSeriesUpToOn r f p S) :
    HasFTaylorSeriesUpToOn r (finiteReflectionExtension r f)
      (finiteReflectionTaylor r p) (finiteReflectionDomain r S) := by
  unfold finiteReflectionExtension finiteReflectionTaylor
  apply HasFTaylorSeriesUpToOn.finset_sum_const_smul
    (I := Finset.univ) (a := finiteReflectionCoeff r)
  intro j hj
  exact (hp.compContinuousLinearMap (finiteReflectionMap r j)).mono (by
    intro z hz
    exact Set.mem_iInter.mp hz j)

lemma finiteReflectionNode_neg (r : ℕ) (j : Fin (r + 1)) :
    finiteReflectionNode r j < 0 := by
  simp only [finiteReflectionNode, neg_lt_zero]
  positivity

/-- If `S` lies in the upper half-space, its common reflected preimage meets `S`
only on the boundary hyperplane. -/
lemma normal_eq_zero_of_mem_inter_finiteReflectionDomain
    (r : ℕ) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hSupper : S ⊆ {z | 0 ≤ z 0}) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ S ∩ finiteReflectionDomain r S) : z 0 = 0 := by
  have hz_nonneg : 0 ≤ z 0 := hSupper hz.1
  have hz_reflected : finiteReflectionMap r (0 : Fin (r + 1)) z ∈ S :=
    Set.mem_iInter.mp hz.2 0
  have hz_reflected_nonneg : 0 ≤ finiteReflectionMap r (0 : Fin (r + 1)) z 0 :=
    hSupper hz_reflected
  rw [finiteReflectionMap_apply_zero] at hz_reflected_nonneg
  have hnode : finiteReflectionNode r (0 : Fin (r + 1)) < 0 := finiteReflectionNode_neg r 0
  nlinarith

/-- Set-theoretic piecewise definition with its classical membership decision fixed in
the definition, so downstream theorem statements do not carry a `DecidablePred`. -/
noncomputable def closedPiecewise (s : Set E) (f g : E → F) : E → F :=
  @Set.piecewise E (fun _ ↦ F) s f g (Classical.decPred _)

@[simp] lemma closedPiecewise_of_mem {s : Set E} {f g : E → F} {x : E} (hx : x ∈ s) :
    closedPiecewise s f g x = f x := by
  simp [closedPiecewise, hx]

@[simp] lemma closedPiecewise_of_notMem {s : Set E} {f g : E → F} {x : E} (hx : x ∉ s) :
    closedPiecewise s f g x = g x := by
  simp [closedPiecewise, hx]

/-- Glue two finite-order Taylor fields across a closed cover.  This is the calculus
lemma used by the finite reflection construction: equality of the Taylor fields on
the seam is the precise compatibility condition, and no ambient extension is assumed. -/
lemma HasFTaylorSeriesUpToOn.piecewise_of_isClosed
    {r : ℕ∞ω} {s t : Set E} (hs : IsClosed s) (ht : IsClosed t)
    {f g : E → F} {p q : E → FormalMultilinearSeries ℝ E F}
    (hp : HasFTaylorSeriesUpToOn r f p s)
    (hq : HasFTaylorSeriesUpToOn r g q t)
    (hpq : ∀ m : ℕ, m ≤ r → Set.EqOn (p · m) (q · m) (s ∩ t)) :
    HasFTaylorSeriesUpToOn r (closedPiecewise s f g)
      (fun x m ↦ closedPiecewise s (p · m) (q · m) x) (s ∪ t) := by
  classical
  let R : E → FormalMultilinearSeries ℝ E F :=
    fun x m ↦ closedPiecewise s (p · m) (q · m) x
  have hRs : ∀ m : ℕ, m ≤ r → Set.EqOn (p · m) (R · m) s := by
    intro m hm x hx
    simp [R, hx]
  have hRt : ∀ m : ℕ, m ≤ r → Set.EqOn (q · m) (R · m) t := by
    intro m hm x hx
    by_cases hxs : x ∈ s
    · simpa [R, hxs] using (hpq m hm ⟨hxs, hx⟩).symm
    · simp [R, hxs]
  have hfs : Set.EqOn (closedPiecewise s f g) f s := by
    intro x hx
    simp [hx]
  have hgt : Set.EqOn (closedPiecewise s f g) g t := by
    intro x hx
    by_cases hxs : x ∈ s
    · have hzero := hpq 0 zero_le ⟨hxs, hx⟩
      have hpf := hp.zero_eq x hxs
      have hqg := hq.zero_eq x hx
      rw [closedPiecewise_of_mem hxs]
      exact hpf.symm.trans ((congrArg ContinuousMultilinearMap.curry0 hzero).trans hqg)
    · simp [hxs]
  have hps : HasFTaylorSeriesUpToOn r (closedPiecewise s f g) R s :=
    (hp.congr hfs).congr_series hRs
  have hqt : HasFTaylorSeriesUpToOn r (closedPiecewise s f g) R t :=
    (hq.congr hgt).congr_series hRt
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hxs | hxt
    · exact hps.zero_eq x hxs
    · exact hqt.zero_eq x hxt
  · intro m hm x hx
    by_cases hxs : x ∈ s
    · by_cases hxt : x ∈ t
      · exact (hps.fderivWithin m hm x hxs).union
          (hqt.fderivWithin m hm x hxt)
      · apply (hps.fderivWithin m hm x hxs).mono_of_mem_nhdsWithin
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        refine ⟨tᶜ, ht.isOpen_compl.mem_nhds hxt, ?_⟩
        intro y hy
        exact hy.2.elim id (fun hyt ↦ (hy.1 hyt).elim)
    · have hxt : x ∈ t := hx.resolve_left hxs
      apply (hqt.fderivWithin m hm x hxt).mono_of_mem_nhdsWithin
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨sᶜ, hs.isOpen_compl.mem_nhds hxs, ?_⟩
      intro y hy
      exact hy.2.elim (fun hys ↦ (hy.1 hys).elim) id
  · intro m hm
    exact (hps.cont m hm).union_of_isClosed (hqt.cont m hm) hs ht

/-- Genuine finite-`C^r` reflection extension on a closed upper-half-space piece.
This is intentionally finite order: the function depends on `r`, so this theorem is
not used as a quantifier swap for the final `C∞` result. -/
lemma finiteReflection_hasFTaylorSeriesUpToOn_union
    (r : ℕ) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hSclosed : IsClosed S) (hSupper : S ⊆ {z | 0 ≤ z 0})
    {f : EuclideanSpace ℝ (Fin n) → F}
    {p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F}
    (hp : HasFTaylorSeriesUpToOn r f p S) :
    HasFTaylorSeriesUpToOn r
      (closedPiecewise S f (finiteReflectionExtension r f))
      (fun x m ↦ closedPiecewise S (p · m) (finiteReflectionTaylor r p · m) x)
      (S ∪ finiteReflectionDomain r S) := by
  apply HasFTaylorSeriesUpToOn.piecewise_of_isClosed
    hSclosed (isClosed_finiteReflectionDomain r hSclosed) hp
    (finiteReflection_hasFTaylorSeriesUpToOn r hp)
  intro m hm z hz
  have hz0 : z 0 = 0 :=
    normal_eq_zero_of_mem_inter_finiteReflectionDomain r hSupper hz
  exact (finiteReflection_taylor_jet_eq r m (by exact_mod_cast hm) p hz0).symm

lemma finiteReflection_contDiffOn_union
    (r : ℕ) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hSclosed : IsClosed S) (hSupper : S ⊆ {z | 0 ≤ z 0})
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ContDiffOn ℝ r f S) (hSunique : UniqueDiffOn ℝ S) :
    ContDiffOn ℝ r (closedPiecewise S f (finiteReflectionExtension r f))
      (S ∪ finiteReflectionDomain r S) := by
  exact (finiteReflection_hasFTaylorSeriesUpToOn_union r hSclosed hSupper
    (hf.ftaylorSeriesWithin hSunique)).contDiffOn

/-! ## A checked local finite-order extension theorem -/

/-- The literal closed half-space used by the standard manifold-with-boundary model. -/
def closedUpperHalfSpace : Set (EuclideanSpace ℝ (Fin n)) := {z | 0 ≤ z 0}

lemma isClosed_closedUpperHalfSpace : IsClosed (closedUpperHalfSpace (n := n)) := by
  change IsClosed ((EuclideanSpace.proj (i := (0 : Fin n))) ⁻¹' Set.Ici 0)
  exact isClosed_Ici.preimage (EuclideanSpace.proj (i := (0 : Fin n))).continuous

lemma convex_closedUpperHalfSpace : Convex ℝ (closedUpperHalfSpace (n := n)) := by
  apply convex_halfSpace_ge
  exact
    { map_add := fun x y ↦ by simp
      map_smul := fun c x ↦ by simp }

/-- A positive-radius closed ball cut by the upper half-space is a unique-differentiability
set, including at a point on its flat boundary. -/
lemma uniqueDiffOn_closedBall_inter_closedUpperHalfSpace
    {x : EuclideanSpace ℝ (Fin n)} {d : ℝ} (hd : 0 < d) (hx0 : x 0 = 0) :
    UniqueDiffOn ℝ (Metric.closedBall x d ∩ closedUpperHalfSpace (n := n)) := by
  apply uniqueDiffOn_convex
    ((convex_closedBall x d).inter convex_closedUpperHalfSpace)
  refine ⟨x + (d / 2) • EuclideanSpace.single 0 (1 : ℝ), ?_⟩
  rw [interior_inter, interior_closedBall x hd.ne']
  constructor
  · rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, EuclideanSpace.norm_single,
      norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hd)]
    exact half_lt_self hd
  · rw [mem_interior]
    refine ⟨{z : EuclideanSpace ℝ (Fin n) | 0 < z 0}, ?_, ?_, ?_⟩
    · intro z hz
      change 0 ≤ z 0
      exact le_of_lt hz
    · change IsOpen ((EuclideanSpace.proj (i := (0 : Fin n))) ⁻¹' Set.Ioi 0)
      exact isOpen_Ioi.preimage (EuclideanSpace.proj (i := (0 : Fin n))).continuous
    · change 0 < x 0 + (d / 2) * (EuclideanSpace.single 0 (1 : ℝ)) 0
      simpa [hx0] using half_pos hd

/-- An explicit finite intersection of open balls on which the finite reflection formula
only samples the chosen closed ball. -/
def finiteReflectionNeighborhood (r : ℕ) (x : EuclideanSpace ℝ (Fin n)) (d : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.ball x d ∩
    ⋂ j : Fin (r + 1), finiteReflectionMap r j ⁻¹' Metric.ball x d

lemma isOpen_finiteReflectionNeighborhood (r : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (d : ℝ) :
    IsOpen (finiteReflectionNeighborhood r x d) := by
  apply Metric.isOpen_ball.inter
  apply isOpen_iInter_of_finite
  intro j
  exact Metric.isOpen_ball.preimage (finiteReflectionMap r j).continuous

lemma mem_finiteReflectionNeighborhood_self (r : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} {d : ℝ} (hd : 0 < d) (hx0 : x 0 = 0) :
    x ∈ finiteReflectionNeighborhood r x d := by
  refine ⟨Metric.mem_ball_self hd, Set.mem_iInter.mpr ?_⟩
  intro j
  change finiteReflectionMap r j x ∈ Metric.ball x d
  rw [finiteReflectionMap_of_normal_eq_zero r j hx0]
  exact Metric.mem_ball_self hd

lemma finiteReflectionNeighborhood_subset_ball (r : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (d : ℝ) :
    finiteReflectionNeighborhood r x d ⊆ Metric.ball x d :=
  inter_subset_left

lemma finiteReflectionNeighborhood_subset_reflection_union (r : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (d : ℝ) :
    finiteReflectionNeighborhood r x d ⊆
      (Metric.closedBall x d ∩ closedUpperHalfSpace (n := n)) ∪
        finiteReflectionDomain r
          (Metric.closedBall x d ∩ closedUpperHalfSpace (n := n)) := by
  intro z hz
  by_cases hz0 : 0 ≤ z 0
  · exact Or.inl ⟨Metric.ball_subset_closedBall hz.1, hz0⟩
  · apply Or.inr
    unfold finiteReflectionDomain
    rw [Set.mem_iInter]
    intro j
    refine ⟨Metric.ball_subset_closedBall (Set.mem_iInter.mp hz.2 j), ?_⟩
    change 0 ≤ finiteReflectionMap r j z 0
    rw [finiteReflectionMap_apply_zero]
    have hj : finiteReflectionNode r j < 0 := finiteReflectionNode_neg r j
    have hzneg : z 0 < 0 := lt_of_not_ge hz0
    nlinarith

/-- The promised independently useful finite-order theorem.  For each fixed `r` it produces
one ambient `C^r` function; the dependence on `r` is explicit and therefore cannot be used to
fake a single `C∞` extension by swapping quantifiers. -/
lemma finite_contDiffOn_closedUpperHalfSpace_exists_open_extension_at
    (r : ℕ) {W : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hW : IsOpen W) {x : EuclideanSpace ℝ (Fin n)} (hxW : x ∈ W)
    (hx0 : x 0 = 0)
    (hf : ContDiffOn ℝ r f (W ∩ closedUpperHalfSpace (n := n))) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧
      ∃ g : EuclideanSpace ℝ (Fin n) → F,
        ContDiffOn ℝ r g V ∧
        Set.EqOn g f (V ∩ closedUpperHalfSpace (n := n)) := by
  obtain ⟨d, hd, hdW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds hxW)
  let S : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.closedBall x d ∩ closedUpperHalfSpace (n := n)
  have hSclosed : IsClosed S :=
    Metric.isClosed_closedBall.inter isClosed_closedUpperHalfSpace
  have hSupper : S ⊆ {z | 0 ≤ z 0} := inter_subset_right
  have hSunique : UniqueDiffOn ℝ S :=
    uniqueDiffOn_closedBall_inter_closedUpperHalfSpace hd hx0
  have hfS : ContDiffOn ℝ r f S := by
    apply hf.mono
    intro z hz
    exact ⟨hdW hz.1, hz.2⟩
  let g : EuclideanSpace ℝ (Fin n) → F :=
    closedPiecewise S f (finiteReflectionExtension r f)
  have hgUnion : ContDiffOn ℝ r g (S ∪ finiteReflectionDomain r S) :=
    finiteReflection_contDiffOn_union r hSclosed hSupper hfS hSunique
  refine ⟨finiteReflectionNeighborhood r x d,
    isOpen_finiteReflectionNeighborhood r x d,
    mem_finiteReflectionNeighborhood_self r hd hx0, ?_, g, ?_, ?_⟩
  · intro z hz
    exact hdW (Metric.ball_subset_closedBall hz.1)
  · exact hgUnion.mono (finiteReflectionNeighborhood_subset_reflection_union r x d)
  · intro z hz
    apply closedPiecewise_of_mem
    exact ⟨Metric.ball_subset_closedBall hz.1.1, hz.2⟩

end LeeSmooth.SeeleyExtension
