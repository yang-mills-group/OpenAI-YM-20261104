import YM.Integration.WilsonMatrixTicketLanesNativePrices

/-! Uniqueness of the complete formal Wilson source in the two perturbative prescriptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesNativeFields
open Lattice FVA2 MS MS.Local.Physical MS.Cylinder MS.Cylinder.Lab
open scoped Classical BigOperators
variable {G : Gauge}

/-- On every torus, both fields have the entire Taylor germ of the very same nonlinear observable. -/
theorem field (V : Warehouse G) (d : ℕ) (j : V.Atom d) :
    V.artifact d j = FVAAlt2.Shop.origin (V.S d) j := by
  apply (markEq ..).mp
  apply Filter.Eventually.of_forall
  intro n
  apply Subtype.ext
  have x := ((V.poised d j).pays n (0 : Site n)).home
  have y := (FVAAlt2.Shop.field_ok (V.S d) j (V.h d) (V.acts d) (0 : Site n)).stamp
  change ((Shift 0 (shown n (FVAAlt2.Shop.origin (V.S d) j))).val) = _ at y
  simpa only [shift_nil] using x.trans y.symm

/-- Equality includes the input field's full finite Wick compensation at every declared grade. -/
theorem menu (V : Warehouse G) (B : Deck G) (d k : ℕ) (u : B.BIndex (d:ℤ) k) :
    (V.native B).inkM d k u =
      (FVAAlt2.Shop.richBook B V.F V.H V.S V.h V.acts).menu d k u := by
  change (∑ j : V.Atom d, (V.prices B d k u j : ℂ) • V.inkB d j) =
    ∑ j : V.Atom d, FVAAlt2.Shop.valueP B (V.S d) (V.h d) (V.acts d) u j •
      FVAAlt2.Shop.priceS (V.S d) j
  apply Finset.sum_congr rfl
  intro j _
  rw [WilsonMatrixTicketLanesNativePrices.columns]
  unfold Warehouse.inkB FVAAlt2.Shop.priceS
  rw [field]

end YM.Integration.WilsonMatrixTicketLanesNativeFields
