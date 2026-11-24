import YangMills.LatticeFields
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Isomorphisms

/-! Canonical representatives in the declared finite raw Wilson coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Wilson
open Function Submodule
open scoped InnerProductSpace
variable {g : GaugeGroup} {B : Maxwell.Reference g} {C : WilsonFamily g}
  {D : WilsonData B C} {T : Hierarchy C}

abbrev RawHilbert (D : WilsonData B C) (d : ℕ) := EuclideanSpace ℂ (Fin (D.raw.width d))

/-- Choose the representative perpendicular to all raw insertions with zero
physical image, using the standard Hermitian metric in the declared coordinates. -/
def OrthogonalLift (D : WilsonData B C) (T : Hierarchy C) (d : ℕ) (v : T.Field d)
    (u : RawHilbert D d) : Prop :=
  T.project (D.raw.token ⟨d, u.ofLp⟩) = ⟨d, v⟩ ∧
    ∀ z : RawHilbert D d, T.project (D.raw.token ⟨d, z.ofLp⟩) = ⟨d, 0⟩ → inner ℂ z u = 0

/-- For fixed raw coordinates and physical projection the lift is uniquely
determined at each grade, linear, and shared by every radius and insertion. -/
theorem WilsonData.AdjointOn.orthogonalSection (h : D.AdjointOn T) (d : ℕ) :
    ∃! lift : T.Field d →ₗ[ℂ] RawHilbert D d, ∀ v, OrthogonalLift D T d v (lift v) := by
  choose π reads using h.quotient
  have onto (e : ℕ) : Surjective (π e) := by
    intro v
    obtain ⟨token, ht⟩ := h.covers ⟨e, v⟩
    obtain ⟨⟨e', z⟩, rfl⟩ := D.raw.onto token
    have equal := (reads e' z).symm.trans ht
    cases equal
    exact ⟨z, rfl⟩
  let coords := WithLp.linearEquiv 2 ℂ (RawSpace (D.raw.width d))
  let q : RawHilbert D d →ₗ[ℂ] T.Field d := π d ∘ₗ coords.toLinearMap
  let K := q.ker
  let toField := q.quotKerEquivOfSurjective ((onto d).comp coords.surjective)
  let toOrth := K.quotientEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  let L : T.Field d →ₗ[ℂ] RawHilbert D d := Kᗮ.subtype ∘ₗ toOrth.toLinearMap ∘ₗ toField.symm.toLinearMap
  have read (u : RawHilbert D d) : T.project (D.raw.token ⟨d, u.ofLp⟩) = ⟨d, q u⟩ := reads d u.ofLp
  have proj (v : T.Field d) : q (L v) = v := by
    change toField (Submodule.Quotient.mk (toOrth (toField.symm v)).val) = v
    rw [Submodule.mk_quotientEquivOfIsCompl_apply, toField.apply_symm_apply]
  have law (v : T.Field d) : OrthogonalLift D T d v (L v) := by
    refine ⟨(read (L v)).trans (congrArg (Sigma.mk d) (proj v)), fun z hz => ?_⟩
    have zero : q z = 0 := sigma_mk_injective ((read z).symm.trans hz)
    exact (toOrth (toField.symm v)).property z (LinearMap.mem_ker.mpr zero)
  refine ⟨L, law, fun lift hl => ?_⟩
  ext v : 1
  have same : q (lift v) = v := sigma_mk_injective ((read (lift v)).symm.trans (hl v).1)
  have null : lift v - L v ∈ K := by
    change q (lift v - L v) = 0
    rw [map_sub, same, proj, sub_self]
  have orth : lift v - L v ∈ Kᗮ := by
    apply Submodule.sub_mem
    · intro z hz
      exact (hl v).2 z ((read z).trans (congrArg (Sigma.mk d) (LinearMap.mem_ker.mp hz)))
    · exact (toOrth (toField.symm v)).property
  exact sub_eq_zero.mp ((Submodule.disjoint_def.mp K.isCompl_orthogonal.disjoint) _ null orth)

end YangMills.Wilson
#print axioms YangMills.Wilson.WilsonData.AdjointOn.orthogonalSection
