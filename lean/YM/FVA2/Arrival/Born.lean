import YM.FVA2.Full.Stated
import YM.FVA2.Arrival.Folio
/-!
# Physical Taylor objects from the stencils $B^a_h$

`Birth`: a physical label (see `theory`) and a point of insertion. Its data use the literal
row-label (`MS.Menus.Glyph`; horizon here is an upper bound on size; keep the own size of
the label). No external dimension charge for the change to physical length units initially.

`Birth.words`: full, not connected, formal joint moments including the Laurent steps and top
Wick compensations, lattice units. This is the reading before multiplying by those spacing factors.
Use it as the prescription. `accord` for relating it to the literal `XSpace` reports
(`Handoff.lean` also gives the interpretation in physical length units and
inside the closure from the multiscale Epoch format).

Local notation `ν` here just for the real-to-complex power series inclusion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Arrival
open Function Set Filter Finset MeasureTheory Lattice Wilson Press XPos Change Slice
open MS MS.Koszul MS.Book Convolve Program MS.Native MS.Theater MS.Menus MS.Rake
open MS.Orbit MS.Fleet MS.Tide MS.Swirl MS.Swirl.Near
open FormalOPE.RG10.MultiGauge Splice Maxwell Maxwell.Free
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {W: Type} {k:ℕ} (Y:XSpace.Initialize G)
local notation "B"=> portDeck G
structure Birth (G:Gauge) where
    horizon : ℕ
    glyph : Glyph (portDeck G) horizon
    at' : Cover
namespace Birth
variable (i:Birth G)
-- independent coefficient assembly
abbrev Char (i: Birth G):= i.glyph.Bundle
def chooses (j:i.Char) : Folio G:= ⟨ i.horizon,i.glyph,j,i.at'⟩
def scan {U:Type}[AddCommMonoid U] : List (Birth G)→ (List (Folio G)→ U) → U
    | [], read=> read []
    | i::l, read=> ∑ j:Char i, scan l (fun x=> read (chooses i j :: x))
def words (n:Side)(v:List (Birth G)):PowerSeries ℝ:= scan v (Folio.coefficients Y n)
-- scan distributes under either type of coefficient ticket. `List` product transparent.
lemma dist {U D:Type}[AddCommMonoid U][AddCommMonoid D]{F : List (Folio G) → U}(X: U →+ D) (l:List (Birth G)): X (scan l F)=scan l (X∘ F):= by induction l generalizing F with| nil=> rfl | cons i l ih=> simp_rw [ scan,map_sum, ih ]; rfl
lemma scan_prod {U:Type}[CommSemiring U] (X:Folio G→ U)(v: List (Birth G)): scan v (fun l=> (l.map X).prod)=(v.map fun i=>∑ j:Char i,X (chooses i j)).prod:= by
 induction v with
 | nil=> rfl
 | cons i v h=> simp only [scan,List.map_cons,List.prod_cons,←h,sum_mul]; apply sum_congr rfl; intro j _; exact (dist (AddMonoidHom.mulLeft (X (i.chooses j))) v).symm
variable (n:Side)
local notation "E"=> Transverse G n
def broad : Ticket (Transverse G n):= ∑ j:i.Char,Folio.loan Y (i.chooses j) n
local notation "Π"=> Ticket (Transverse G n)
def kVector (v:List (Birth G)) := (v.map fun i=>broad Y i n).prod
variable {A J:Type} [Fintype J][DecidableEq J](a:Axes G n A J)(μ:Measure (Transverse G n))[Measure.IsAddHaarMeasure μ](ev:Even n.val)
include ev
private def reads : Ticket E →+ PowerSeries ℝ := (AddMonoidHom.mulRight ((input (gaussian G n) μ a.relative)⁻¹)).comp ((input (gaussian G n) μ).comp (AddMonoidHom.mulLeft a.relative))
lemma priced (l:List (Birth G)): words Y n l=a.sumBody μ (kVector Y n l):= by
 let L:=reads n a μ; change scan l _= L (kVector Y n l); rw [show Folio.coefficients Y n=L ∘ Folio.pose Y n from funext (fun p=> Folio.loan_full Y p a μ ev), ← dist, show kVector Y n l= _ from (scan_prod (fun i=> Folio.loan Y i n) l).symm]; rfl
omit ev
-- compatibility of the exact native columns with XSpace's physical Maxwell labels
variable (c:Glyph (portDeck G) k)
-- size cost in units of this label, later. Keep grade from free slot.
lemma estuary : Free.bwt (G:=G)=(fun i=> (Free.scaleW i,1)):= rfl
def theory (c:Glyph (portDeck G) k) : XSpace.On.Grade G c.size:=
   ⟨ Theater.Letters B c, Theater.letter_sector B c, fun v hv=> by
        have hp:= re_grade (Theater.film B c.2.2 (h:=c.size)) ( (cinema _).mp (filmW B c.2.2)|>.1 ); have hz:= congr_arg Prod.fst (hp hv); simpa [ Free.bwt, Finsupp.weight_apply,Finsupp.sum, Prod.fst_sum ] using! hz ⟩
variable {R:XSpace.Period} (T:R.Tree)
lemma vent : XSpace.On.sectionMap c.size ⟨(theory c).val,(theory c).property.1⟩=beginning c.2.2:= Subtype.ext (film_eq (w:=c.size) (r:=c.grade) c.2.2).symm
def entered (i:Birth G) := XSpace.On.stencil Y.hol (Y.surveys i.glyph.size) R T (wrap R.side i.at') (theory i.glyph)
lemma tabulate : entered Y T i=∑ j:i.Char, Folio.peg Y T (i.chooses j):= by
 let g := i.glyph; change XSpace.Bare.column T (Y.surveys g.size) (wrap R.side i.at') ( XSpace.On.sectionMap g.size ⟨ (theory g).val,(theory g).property.1 ⟩ )= _; rw [vent,XSpace.Bare.column_formula, Press.compact, AddSubmonoidClass.coe_finsetSum,XSpace.Bare.raw,map_sum]; exact sum_congr rfl fun _ _=> rfl
local notation "ν"=> PowerSeries.map Complex.ofRealHom
variable (l:List (Birth G))
theorem accord : XSpace.Bare.normalized T G (l.map (entered Y T)).prod = ν (words Y R.side l):= by
 let X := (XSpace.Bare.normalized T G).toAddMonoidHom; have hb : (ν).toAddMonoidHom ∘ Folio.coefficients Y R.side= X ∘ Folio.money Y T:= funext fun l=>(Folio.X_wick T Y l).symm; change _= (ν).toAddMonoidHom _; unfold words; rw [dist,hb,← dist, show scan l (Folio.money Y T)=_ from scan_prod (Folio.peg Y T) l]; rw [ show entered Y T= _ from funext fun i=> tabulate Y i T ]; rfl -- definitional (`X`)
lemma compact_labels (l: Finset W)(x:W→Cover) (d:W→ℕ)(v:(w:W)→ Glyph B (d w)) : XSpace.Bare.normalized T G ( ∏ i∈l, XSpace.On.stencil Y.hol (Y.surveys (v i).size) R T (wrap R.side (x i)) (theory (v i)) )= ν (words Y R.side (l.toList.map fun i=> (⟨ d i,v i,x i⟩:Birth G))):= by
 rw [← accord, List.map_map]; congr 1; exact (Finset.prod_map_toList l fun i=> entered Y T (⟨ d i,v i,x i⟩:Birth G)).symm
end Birth

end YM.FVA2.Arrival
