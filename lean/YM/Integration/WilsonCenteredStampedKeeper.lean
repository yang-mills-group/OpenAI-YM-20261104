import YM.Planned.ATOM_GUARDED_LAYOUT.Guards
import YM.QuadraticLocal.Kiosk

/-! Recover the physical hard host directly from the actual second merge of
a marked date, preserving its own representation on every group field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredStampedKeeper
open Finset RG Lattice Wilson Push.Local Ovens QuadraticLocal Progress.DirectedRecipe Planned.GuardedAtom
open scoped Classical BigOperators
variable {G : Gauge} {n : Side}

def docket : Dummy n ↪ Foot n×ℕ where
  toFun s := (⟨s.1.val.1,s.1.val.2,s.1.property.1,s.1.property.2⟩,s.2)
  inj' _ _ h:=Prod.ext (Subtype.ext (Prod.ext (congr_arg (fun x=>x.1.support) h)
    (congr_arg (fun x=>x.1.inventory) h))) (congr_arg (fun t : Foot n×ℕ=>t.2) h)

def projected (P : Rep G n) (register : P.activities.forced=Ovens.Pipes.addr (folio G n) P.p) :
    Guard.Keeper P.p P.activities where
  code:=docket.trans (sleepK G n)
  support s:=register.symm ▸ congr_arg Foot.support (tile_exact (G:=G) P.p (docket s).1 s.2)
  inventory s:=register.symm ▸ congr_arg Foot.inventory (tile_exact (G:=G) P.p (docket s).1 s.2)
  pass s U:=by
    rw [register]
    intro holds
    change (Ovens.Pipes.addr (folio ..) P.p (sleepK G n (docket s))).extraTest U
    apply (tile_test P.p (docket s).1 s.2 U).2
    have shape:=tile_exact (G:=G) P.p (docket s).1 s.2
    exact (congr_arg₂ (fun x y : Foot n=>x.support∩flags P.p.threshold U=y.inventory) shape shape) ▸ holds

def original (P : Rep G n) {A : Activities G n} {e f a r : ℝ}
    (second : Kiosk.Second P.p A P.activities e f a r) : Guard.Keeper P.p P.activities :=
  projected P second.projection

end YM.Integration.WilsonCenteredStampedKeeper
