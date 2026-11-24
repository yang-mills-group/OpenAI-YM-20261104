import YM.FVA2.Catalog

/-!
# Specialization to all fields/marks of LitBook

Relates each scheme field (its register matrix allowed to depend on the log)
to the prescribed Wilson coefficients, including the unmarked region.
Note the `proof` (antifields for exact classes) is not used in `rent` and
thus has no effect on these normalized gauge observables.

At this point not assuming or claiming their continuum equality yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Catalog
open Function Set Filter Finset Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit MS.Orbit.Cog
open MS.Orbit.LogReal MS.Bare MS.Cylinder MS.Cylinder.Taylor MS.Puff MS.Puff.Mom MS.Book
open MS.Book.Convolve MS.Book.Program MS.Puff.Engine MS.Swirl.Near MS.Cylinder.Lab MS.Native.Wilsonian MS.Puff.Actors MS.Fleet
open MS.Menus MS.Local.Physical
open PertExtension PertExtension.Orb Substitute Matrix Inversion Coupling Ends Inserted
open scoped Classical Topology ContDiff
variable {G:Gauge} {n:Side} {W: Type} [LinearOrder W]

variable {B : Deck G}(F:LitBook B)(d: W→ℕ)(X:(i:W)→Acts B (d i))
local notation "Y!"=> ℕ

/-- Pulls back the polynomial stencil to invariant observable of the chart.
For a concrete prescription one can fix any such stencil realizations; the
finite result applies to each. Choice here can be used unchanged for all
branches and field horizons. -/
def realized {u v:ℕ}(i: B.BIndex u v) : Unscaled G:={
    degree:=v
    stencil:= F.stamp u v i
    bottom:= (F.levels u v i).low
    stencilVal n:= (F.levels u v i|>.pay n).choose
    invariant n:= (F.levels u v i|>.pay n).choose_spec.1
    chart n:= (F.levels u v i|>.pay n).choose_spec.2.1
    usesStencil n:= (F.levels u v i|>.pay n).choose_spec.2.2 }

def allV (i:W) (x:Glyph B (d i)): Unscaled G:= realized F x.2.2
def allK (i:W)(g:Glyph B (d i))(x:ℝ) (k:ℕ) := oil (X i) g k x
lemma price_bill (p:Team)(i:W) : Menus.rent F (Stripped p) (X i)= pricing p (allV F d) (allK d X) i:= by
    funext x j; unfold Menus.rent pricing; rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun t _=>?_ ; unfold Glyph.preamble; rw [ strip_wobble ]; rfl

theorem Spool_fromAction (h:Even n.val) (p:Team)(x:ℝ)(s:Finset W)(c:W→Cover)(a:Cover) :
    PhysicalSum G p x n true s c a (fun i=> Menus.rent F (Stripped p) (X i))
        (receipt p x a c (allV F d) (allK d X) n s):= by
   simp_rw [price_bill F d X p]; exact blend a c p x h _ _ s
-- any actor at no marks; vacuum itself not normalized intermination
lemma without_fields (p:Team)(x:ℝ)(c:W→Cover)(a:Cover)(V:W→Actor G) : PhysicalSum G p x n true ∅ c a V Trunk.unit:= by
   unfold PhysicalSum Endμ; rw [ show Font _ _ (∅:Finset W)=(PermV σbranch).unit from Puff.Stencil.simple_E _ _ _ (show Marks V x n a c ∅=0 from mark_off (by simp) ..), (PermV _).identityR, Trunk.identityR]
end YM.FVA2.Catalog
