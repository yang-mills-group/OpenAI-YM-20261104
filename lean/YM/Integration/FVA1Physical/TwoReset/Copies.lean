import YM.QuadraticLocal.Earn.Rendering
import YM.Integration.FVA1Physical.TwoReset.Period

/-! Repeat unmasked input atoms on larger covers. `page` supplies an indexing
convention for finite fibres, and the passports in this file are FORMAL ONLY —
the stencils and numerical estimates at the original period use the original wallets,
not moving the tests, and in particular not jettisoning any edges. The only thing
we read from the formal binders on larger covers is the centre and mode. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Lattice RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Row Finset
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V α : Type} [DecidableEq V] {n N : Side}
variable {J : Passport n V} {R : Census V} (W : n.val ∣ N.val)

abbrev Pages (n N : Side) := (N.val / n.val)^4

def page (x : Site n) : Fin (Pages n N) ≃ ↑(parcel (splitter W) x) :=
  ( (Finset.equivFin (parcel (splitter W) x)).trans (finCongr ((coverWin W).fold x)) ).symm

protected def coverPassport (J : Passport n V) (u : Fin (Pages n N)) : Passport N V :=
  Passport.point fun i => (page W (J.origin i) u).val

variable (Y : Row J R G α)
protected def copy (u : Fin (Pages n N)) : Row (TwoReset.coverPassport W J u) R G α :=
  { Y with binder :=
    { mode := Y.mode
      front := Y.binder.front
      east := Y.binder.east
      path a := Cable.link ((page W Y.center u).val) ((page W (J.origin a) u).val)
      span _ _ := Cable.link_stop ..
      extra := Y.binder.extra } }

theorem recenter (u : Fin (Pages n N)) :
    (TwoReset.copy W Y u).center = (page W Y.center u).val := rfl

theorem pages {α : Type} [AddCommMonoid α] (z : Site n) (F : Site N → α) :
    ∑ u : Fin (Pages n N), F (page W z u).val = ∑ x ∈ parcel (splitter W) z, F x := by
  rw [← Finset.sum_attach _ F]
  exact Equiv.sum_comp (page W z) (fun x=> F x.val)

end YM.Integration.FVA1Physical.TwoReset
