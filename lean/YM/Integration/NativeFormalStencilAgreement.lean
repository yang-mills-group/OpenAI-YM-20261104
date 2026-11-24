import YM.Integration.NativeFormalDeckAgreement
import YM.FVA2.LiftedLabels
import YM.FVAAlt2.Home.Turn

/-! The full marked Wilson source and every coefficient of the purchased
rich stencil agree with the physical FVA2 warehouse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalStencilAgreement

open Lattice MS.Local.Physical MS.Land
open MS.Cylinder.Lab
open FVA2

variable {G : Gauge}

/-- The periodic evaluations determine the full infinite-lattice Taylor stencil. -/
theorem source (V : Warehouse G) (d : ℕ) (i : V.Atom d) :
    FVAAlt2.Shop.origin (V.S d) i = V.artifact d i := by
  apply (enterEq _ _).mp
  apply Filter.Eventually.of_forall
  intro n
  rw [FVAAlt2.Shop.doc_co]
  have h := ((V.poised d i).pays n 0).home
  rw [show enters n (V.artifact d i) = (shown n (V.artifact d i)).val from rfl]
  rw [shift_nil, Plate.bare_put] at h
  exact h.symm

/-- The inverse physical top matrix prices identical stencils for every
weight, rank and perturbative order. -/
theorem menu (V : Warehouse G) (B : Deck G) (d r : ℕ) (u : B.BIndex d r) :
    (FVAAlt2.Shop.richBook B V.F V.H V.S V.h V.acts).menu d r u =
      (V.native B).inkM d r u := by
  change FVAAlt2.Shop.RBook B (V.S d) (V.h d) (V.acts d) u = _
  rw [← FVAAlt2.Home.funds]
  change (∑ j : V.Atom d, (V.qfits B d r u j) • FVAAlt2.Shop.priceS (V.S d) j) =
    ∑ j : V.Atom d, (↑(V.prices B d r u j) : ℂ) • V.inkB d j
  apply Finset.sum_congr rfl
  intro j _
  rw [V.price_cast B u j]
  exact congrArg (fun z => V.qfits B d r u j • MS.Book.levels (V.grade d j) z) (source V d j)

end YM.Integration.NativeFormalStencilAgreement
end
