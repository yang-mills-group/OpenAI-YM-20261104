import YM.Push.CORRECTED_COLUMNS.Program
/-!
# Coefficients of a singleton insertion

`chunk` applies the inverse terminal coordinate map to the given field
label at cutoff `N` and period `p`. It then reads the factory's coefficient
at level `m` on that same family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Issue
open RG Marker Cells Wilson Lattice MeasureTheory Function
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {r k N p : ℕ} {B : Wire C r k N p} {d : ℕ}






def chunk (C : Family G) (v : C.label d) (m N p : ℕ) : Source.Coefficient (C.labels.level d) (C.side m p) :=
    (C.factory d N p).entries m ((C.factory d N p).terminal.symm v)







end YM.Push.Corrected.Issue
