import PoincareConjecture.Topology.FiberSaturation.ClosedRealRelation

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CircleBundle
open Set Function
variable {F : Type*} [TopologicalSpace F]

/-- Comparison induced by the explicit seam and the complete integer orbit. -/
def closedToReal (φ : F ≃ₜ F) {L : ℝ} (hL : 0 < L) :
    ClosedMappingTorus φ L → MappingTorus.Space φ.symm L :=
  Quot.lift (fundamentalProjection φ L)
    (fun p r h => (fundamentalProjection_eq_iff_seam φ hL p r).mpr h)

@[simp] theorem closedToReal_mk (φ : F ≃ₜ F) {L : ℝ} (hL : 0 < L)
    (p : F × Icc (0 : ℝ) L) :
    closedToReal φ hL (Quot.mk _ p) = MappingTorus.proj φ.symm L (p.1,(p.2 : ℝ)) := rfl

theorem continuous_closedToReal (φ : F ≃ₜ F) {L : ℝ} (hL : 0 < L) :
    Continuous (closedToReal φ hL) :=
  continuous_quot_lift _ (continuous_fundamentalProjection φ L)

theorem bijective_closedToReal (φ : F ≃ₜ F) {L : ℝ} (hL : 0 < L) :
    Bijective (closedToReal φ hL) := by
  constructor
  · intro a b
    induction a using Quot.inductionOn with
    | h p =>
      induction b using Quot.inductionOn with
      | h r =>
        intro h
        exact Quot.sound ((fundamentalProjection_eq_iff_seam φ hL p r).mp h)
  · intro z
    obtain ⟨p,hp⟩ := surjective_fundamentalProjection φ hL z
    exact ⟨Quot.mk _ p,hp⟩

/-- Both original quotient topologies are retained. The inverse is continuous
by compactness of the finite cylinder and the proved Hausdorff orbit quotient. -/
def closedRealHomeomorph [CompactSpace F] [T2Space F] (φ : F ≃ₜ F)
    {L : ℝ} (hL : 0 < L) : ClosedMappingTorus φ L ≃ₜ MappingTorus.Space φ.symm L := by
  letI : T2Space (MappingTorus.Space φ.symm L) := MappingTorus.space_t2Space φ.symm hL
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (closedToReal φ hL) (bijective_closedToReal φ hL))
    (continuous_closedToReal φ hL)

@[simp] theorem closedRealHomeomorph_mk [CompactSpace F] [T2Space F] (φ : F ≃ₜ F)
    {L : ℝ} (hL : 0 < L) (p : F × Icc (0 : ℝ) L) :
    closedRealHomeomorph φ hL (Quot.mk _ p) = fundamentalProjection φ L p := rfl

/-- Representative compatibility characterizes the comparison, not just its type. -/
theorem closedRealHomeomorph_unique [CompactSpace F] [T2Space F] (φ : F ≃ₜ F)
    {L : ℝ} (hL : 0 < L) (e : ClosedMappingTorus φ L ≃ₜ MappingTorus.Space φ.symm L)
    (he : ∀ p : F × Icc (0 : ℝ) L, e (Quot.mk _ p) = fundamentalProjection φ L p) :
    e = closedRealHomeomorph φ hL := by
  apply Homeomorph.ext
  intro z
  induction z using Quot.inductionOn with
  | h p => exact he p

end PoincareConjecture.Topology.FiberSaturation.CircleBundle
