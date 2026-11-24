import YM.MS.Echo.Dusk
/-!
Eventual identity of merged insertions modulo exact primitive through given order.
A generalized `θ^-1` ticket allows telescoping through all marked slots. It returns a *single*
primitive at any fixed native placement array. Actual closure theorem consumes it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Echo
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Native
open Lattice Book Convolve Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Flux City Signal Modeled Frame Wire Latch Job Belt Rake Orbit Orbit.LogReal Vista High.Knobs Fleet Rake.Geo
open Puff Puff.SplitP Puff.Engine Puff.Actors
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W]{G:Gauge}{n i k:ℕ}{ A U Y:W→ Actor G }{φ F H V: Actor G}{u:ℤ}{s:Finset W}{P:Cover}{p:Team}{y:ℝ}
   {z:W→ Cover}{c:Berth ( I:=I ) ( W:=W )}{l:Filter I}{v w:W}
set_option quotPrecheck false
local notation "B"=> Spectrum G
local infixl:70 " ⋄ "=> (native G).core
abbrev ghostM (y:ℝ):= steadyE B (style G p y)
lemma eq_shift (h: similar (ghostM (p:=p) y ( F y )) ( H y-V y ) n) (J:Cover): similar (ghostM (p:=p) y ( promote (Lab.Shift J) ( F y ))) (promote (Lab.Shift J) (H y)-promote (Lab.Shift J) ( V y )) n := by intro i hi; rw [ghostM,← shiftX,← map_sub,promised,(show steadyE _ _ _ _ = _ from h i hi)]; rfl -- rw ghostM implicit
structure Refund (p:Team)(X Y:Actor G)(n:ℕ) (s:ℝ) : Prop where
    ticket : ∃ V: Actor G, Circle G V false (-1) ∧ similar (ghostM (p:=p) s ( V s )) ( X s - Y s ) n
lemma Ziff (Y:Actor G): Refund p Y Y n y:= by refine { ticket := ⟨ 0, blank_c ..,?_ ⟩ }; rw [ sub_self ]; intro i hi; exact congr_fun (map_zero ( actB B+blocks B (style G p y))) i
-- add compatible primitives. General Circle.H²
lemma circle_p (h:Circle G φ false u)(he:Circle G H false u): Circle G (φ+H) false u:= by
    refine ⟨fun i x=> (h.actual i x).add ( he.actual i x ),fun i=>?_,fun i t=>( h.settled i t ).add ( he.settled i t ),fun i=>Ready.add ( h.tag i ) (he.tag i),fun _ _ z=> Bool.noConfusion z ⟩; obtain ⟨c,H⟩:= h.room i; obtain ⟨v,hv⟩:= he.room i; exact ⟨c+v,fun s=> ( ( H s ).up (by omega) ).add ( ( hv s ).up (by omega)) ⟩ -- colorless namespace
lemma Refund.trans (h:Refund p φ H n y)(hv:Refund p H F n y): Refund p φ F n y:= by
   obtain ⟨ X,hX,HX⟩:=h.ticket; obtain ⟨ Z,hZ,hq⟩:=hv.ticket; refine { ticket:= ⟨X+Z,circle_p hX hZ, fun i hi=>?_ ⟩ }; have he: (ghostM (p:=p) y) ( (X+Z) y )= ghostM (p:=p) y (X y) + ghostM (p:=p) y ( Z y ):= map_add ( actB B + blocks B (style G p y)) _ _; rw [ he,Pi.add_apply, HX i hi,hq i hi ]; simp only [Pi.sub_apply]; abel -- tactic
structure Menu (p:Team)(X Y:Actor G) : Prop where
   send : ∃ V:Actor G, Circle G V false (-1) ∧∀ y:ℝ, ghostM (p:=p) y ( V y )= X y - Y y
lemma Menu.retained (h:Menu p φ F)(n:ℕ)(y:ℝ): Refund p φ F n y:= by rcases h.send with ⟨X,hV,h⟩; exact { ticket:= ⟨ X,hV,fun i _=>congr_fun (h y) i⟩ }
lemma future_M (h:Sparse l c)(hs:w∉s)(hh:∀ i∈s,U i=Y i)(ht:ReadyP p U)(hp:ReadyP p Y)(hm:Menu p ( U w ) ( Y w ))(n:ℕ): ∀ᶠ k in l, ∀ y:ℝ, Refund p ( Memo (starP c k) U ( insert w s ) ) ( Memo (starP c k) Y ( insert w s ) ) n y:= by
   obtain ⟨V,VH,H⟩:=hm.send; obtain ⟨T,hT⟩:=packets VH n; choose L hL using fun i:W=> packets ( ht.badge i ) n; filter_upwards [eventual_M h ht s n,growD (L:=L) ( t:=T ) h hs] with k hB hx y;
   let z:= starP c k; let A:= Memo z U s; let W0:= fun x:ℝ=> promote ( Lab.Shift ( z w ) ) ( V x ); obtain hF:Circle G A false 0:=memory z ht.badge s; obtain hS:NoWeight n ( A y ) (style G p y):= hB y; have hM(y):A y= Memo z Y s y:= congr_fun ( mergeNe ht.badge hp.badge hh z ) y;
   let T i:= (( A i ) ⋄ W0 i ); refine { ticket:= ⟨ T,(by convert! pair_c hF (shift_c ( z w ) VH ) using 1),?_⟩ }; have hN (Z:W→Actor G)(hG:Badge Z)(y:ℝ): Memo z Z (insert w s) y= ( Memo z Z s y ) ⋄ (wordsX z Z {w} y ):= Eq.trans ( congr_fun ( memorep z hG hs ) y ) ( (native _).turns _ (homewords z hG y {w}) _ (structural (fun k=> ( memory _ hG _).actual k y)) );
   have hw : similar ( ghostM (p:=p) y ( W0 y ) ) (wordsX z U {w} y-wordsX z Y {w} y) n:= by rw [ word_m,word_m ]; exact eq_shift (F:=V) (fun j _=> congr_fun ( H y ) j ) ( z w ) -- type X=i etc
   change similar ( ghostM (p:=p) y _ ) ( Memo z U _ y - Memo z Y _ y ) n; rw [ hN U ht.badge, hN Y hp.badge, ← hM y,← map_sub ]; intro i hi; refine ( moveLeib (fun m=> hF.actual m y) ( stamp_M ht.badge hL y ) ( stamp_job ( hT y ) _ ) hx.symm hS i hi ) |>.trans ( keeps_o hw hi |>.1 ) -- ih proofOfs
end YM.MS.Echo
