import YM.FVA2.XPos.Vertices
import YM.FVA2.Press.Subtraction
/-!
# Pieces of the physical alphabet (microscopic stencil & external Laurent valuations)

`Folio.coefficients`: power series, real-valued, in the bare Wilson coupling
variable. From the same `PertExtension.Orb.diag`. Include the full product observable!
Can't compute these quantities by multiplying scalar expectations. In `Arrival/Born.lean`
use these to assemble `Birth.words`, including exactly the W-shifts; carry the same stencils
and their own Laurent factors. Keep the spatial scaling (from lattice to physical length
units) separate. `X_wick` here is the key to interpreting exactly these coefficients in
`XSpace`. Also see `Handoff.lean` for reading them in the conditional form.

Local notation `ν` here just for the complexification of power series of real coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Arrival
open Function Set Filter Finset MeasureTheory Lattice Wilson Press XPos
open PertExtension Series Radial Series.Tested
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge Splice
open MS MS.Koszul MS.Book Convolve Program MS.Land MS.Native MS.Theater MS.Menus MS.Rake
open Change Slice
open scoped BigOperators Topology ContDiff Classical
variable {G:Gauge} {R: XSpace.Period} (T:R.Tree) {W:Type} {d:ℕ}
local notation "B"=> portDeck G
local notation "E"=> T.Field G
variable (Y:XSpace.Initialize G)
structure Folio (G:Gauge) where
 d:ℕ
 u: Glyph (portDeck G) d
 j: u.Bundle
 addr : Cover
namespace Folio
variable (i:Folio G)
def item : Labels.Label G i.u.size := chip Y i.u i.j
def slots : ℕ:= i.u.tally i.j
lemma count : ∀ j∈ (item Y i).val.support, slots i = j.sum fun _ a=> a:= by
 obtain ⟨u,hu⟩:= pure_chip Y i.u i.j; intro j hj; have ht:= (Labels.pure_grade ..).1 hu (MvPolynomial.mem_support_iff.mp hj); rw [Labels.weight_slot] at ht; exact congr_arg Prod.snd ht.symm
lemma real : Labels.conjPol (item Y i).val=(item Y i).val:= by
 rcases i with ⟨_,c,x|x,i⟩; exact congr_arg Subtype.val (reality (w:=c.size) (r:=c.grade) c.2.2); exact (cinema _).mp ( projects_out ( Y.surveys c.size ) c.2.2 x.1.val x.2.val )|>.2.2
-- real stroke. Keep explicit trans

def entry (i:Folio G) := dot (Y.surveys i.u.size) (item Y i).val
def leaf : Change.Stencil (entry Y i):= Press.page _ _ ((item Y i).property.2)
variable (n:Side)
def placard (n:Lattice.Side) (x:Config G n): ℝ:= (leaf Y i).placed n i.addr x
lemma votes (ev:Even n.val): PertExtension.Orb.PreTest (placard Y i n):= Stencil.vote ev (leaf Y i) i.addr
lemma currency : From (entry Y i).val (i.slots):= by
    rw [entry,item, ← stampF]; exact (Glyph.galleryReady (wickInput Y) i.u i.j).low
local notation "T₀"=> Stack.rise
local notation "X"=> PowerSeries.X
local notation "ν"=> PowerSeries.map Complex.ofRealHom


abbrev asset (l:List (Folio G)) : ℕ:= (l.map slots).sum
abbrev scenario (Y:XSpace.Initialize G) (n:Side)(l:List (Folio G)) := Change.joints (fun j=>placard Y j n) l
variable (l:List (Folio G))

/-- Independent from any other continuum prediction. `external` proves the external power rule
is well-posed: the result is in **power series**, measured from those full moments with the
stated precise Laurent shift. -/
def coefficients : PowerSeries ℝ:= Stack.drop (asset l) (PowerSeries.mk (Orb.diag (Orb.restrictedO (scenario Y n l))))
lemma matured (ev:Even n.val) : Orb.PreTest (scenario Y n l):= by induction l with| nil=>exact FVA2.Orbit.Screen.pre_one | cons i l h=> exact Change.pre_pair (votes Y i n ev) h

section Slice
variable {n} {A J:Type} [Fintype J][DecidableEq J] (a:Axes G n A J)(μ:Measure (Transverse G n))[Measure.IsAddHaarMeasure μ]
def loan (i:Folio G) (n:Side) := (leaf Y i).onLandau n i.addr i.slots
local notation "t"=> Transverse G n
local notation "Φ"=> Chart.nation (G:=G) («P»:=Site n)
def pose (n:Lattice.Side) (l:List (Folio G)) := (l.map fun i=>loan Y i n).prod
lemma funded : X ^ asset l * pose Y n l=T₀ (((scenario Y n l) ∘ (Chart.nation (G:=G) («P»:=Site n))) ∘ incCL G n):= by
 let f (l:List (Folio G)):= ((scenario Y n l)∘Φ)∘ incCL G n; let g(i:Folio G):= (placard Y i n∘Φ)∘ incCL G n; have H (l:List (Folio G)) : Cylinder.Taylor.germ (f l):= by induction l with| nil=>exact contDiffAt_const| cons i l h=> exact (Axes.calm ((leaf Y i).crease (n:=n) i.addr)).mul h
 induction l with
 | nil=> change X^0 * 1=T₀ (1:t→ℝ); rw [MultiGauge.Stack.rise_one,pow_zero,one_mul]
 | cons i l ih=>
    change X ^ (slots i+asset l) * (loan Y i n * pose Y n l)=T₀ (g i*f l); rw [MultiGauge.Stack.rise_mul (f:=g i) (Axes.calm ((leaf Y i).crease (n:=n) i.addr)|>.of_le le_top ) (( H l ).of_le le_top ),pow_add, show X ^ slots i * X ^ asset l * (loan Y i n * pose Y n l)=(X^slots i * loan Y i n)*(X^asset l*pose Y n l) from by ring, show X^slots i*loan Y i n=T₀ (g i) from (leaf Y i).giveback i.addr (currency Y i), show X^asset l*pose Y n l=T₀ (f l) from ih]

variable (ev:Even n.val)
include ev
lemma exact_tree : X ^ asset l * a.sumBody μ (pose Y n l)=PowerSeries.mk (Orb.diag (Orb.restrictedO (scenario Y n l))):= by
 rw [← fall a ev μ (matured Y n l ev), show T₀ ((scenario Y n l ∘ Φ) ∘ includeA G n) =_ from (funded Y l).symm ]; unfold Axes.sumBody enjoy; rw [mul_left_comm a.relative, MultiGauge.Stack.taking, mul_assoc]
lemma loan_full : coefficients Y n l=a.sumBody μ (pose Y n l):= by rw [coefficients,← exact_tree Y l a μ ev]; exact MultiGauge.Stack.drop_mul ..
lemma external : X ^ asset l * coefficients Y n l= PowerSeries.mk (Orb.diag (Orb.restrictedO (scenario Y n l))):= by
 let Gm:= Measure.addHaar (G:= Transverse G n); let k:= Change.Dictionary.picked G n; rw [ loan_full Y l k Gm ev, exact_tree Y l k Gm ev ]
lemma trajectory : Tested.Aspiration (fun t':ℝ=> (t'⁻¹)^(asset l) * Orb.preExpectation (scenario Y n l) t') ( Tested.term (coefficients Y n l) ):= by
    have h:= Orb.before_tree_formula ev (Orb.traySpec G) (matured Y n l ev); let D:= Orb.diag (Orb.restrictedO (scenario Y n l)); have hp:= h.shift ( w:=asset l ) (fun i hi=> ?_); swap
    · exact show D i=0 from (by rw [ ← PowerSeries.coeff_mk i D,← show X ^ _ * coefficients Y n l=PowerSeries.mk D from external Y l ev, PowerSeries.coeff_X_pow_mul',if_neg (by omega) ])
    convert! hp using 1; funext i; rw [Tested.term,coefficients,MultiGauge.Stack.drop, PowerSeries.coeff_mk,PowerSeries.coeff_mk]; rfl
end Slice

section XSpace

def peg (T:R.Tree)(i:Folio G) := XSpace.Bare.raw T (Y.surveys i.u.size) (wrap R.side i.addr) ( item Y i ).val
lemma raw_claim (x:Config G n): Complex.ofRealCLM (placard Y i n x)= wheel (Y.surveys i.u.size) (item Y i).val ( expandAt (wrap n i.addr) x ):= by
 let y := wheel (Y.surveys i.u.size) (item Y i).val (expandAt (wrap n i.addr) x); change Complex.ofRealCLM ((wheel (Y.surveys i.u.size) (item Y i).val (expandAt 0 ( Lattice.translate (wrap n i.addr) x ))).re)=_; rw [wrapped]; change (↑(y.re):ℂ)=y; refine Complex.ext rfl ?_; have he: star y=y:= by
    unfold y wheel; rw [← Labels.conj_value]; rw [real]
 exact ( Complex.conj_eq_iff_im.mp he).symm
lemma hire : X ^ i.slots * peg Y T i= XSpace.Taylor.expandTaylor (T.basis G) (Complex.ofRealCLM ∘ (placard Y i R.side ∘ T.links)):= by
 unfold peg; rw [ XSpace.Bare.coefficient_weight T _ _ _ (count Y i) ]; apply congr_arg; funext x; exact (raw_claim Y i _ _).symm
local notation "U"=> (PowerSeries.map (AlgHom.toRingHom (XPos.install G T)))
def money (T:R.Tree)(l:List (Folio G)) := (l.map (peg Y T)).prod
private lemma combined : X ^ asset l * money Y T l=U (T₀ ((scenario Y R.side l) ∘ T.links)):= by
    induction l with
    | nil=> change X^0 * 1=U (T₀ (1:E→ℝ)); rw [ pow_zero,one_mul,MultiGauge.Stack.rise_one,map_one]
    | cons i l ih=>
       let f:= placard Y i R.side ∘ T.links; let g:= scenario Y R.side l ∘ T.links; have hv:ContDiffAt ℝ ∞ f 0:= hears T (votes Y i R.side (eve _)); have ht:ContDiffAt ℝ ∞ g 0:= hears T (matured Y R.side l (eve _)); change X^(slots i+asset l)*(peg Y T i*money Y T l)=U (T₀ (f*g)); rw [MultiGauge.Stack.rise_mul hv ht,map_mul,pow_add, show X^slots i*X^asset l * (peg Y T i*money Y T l)=(X^slots i * peg Y T i)*(X^asset l*money Y T l) from by ring,ih,hire, ← XPos.parse T f hv]
lemma X_wires : X ^ asset l * XSpace.Bare.normalized T G ( money Y T l )= ν (PowerSeries.mk ( Orb.diag ( Orb.restrictedO (scenario Y R.side l) ))):= by
 rw [← XSpace.Bare.normalized_scalar T, XSpace.Bare.scalar,map_pow,PowerSeries.map_X, combined, XPos.parse T _ (hears T (matured Y R.side l (eve _))) ]; exact XPos.genuine_X T (matured Y R.side l (eve _))
theorem X_wick : XSpace.Bare.normalized T G ( money Y T l )= ν (coefficients Y R.side l):= by
 apply mul_left_cancel₀ (show (X^(asset l):PowerSeries ℂ)≠0 from pow_ne_zero _ PowerSeries.X_ne_zero); rw [X_wires, ← external Y l (eve R),map_mul,map_pow,PowerSeries.map_X]
end XSpace
end Folio
end YM.FVA2.Arrival
