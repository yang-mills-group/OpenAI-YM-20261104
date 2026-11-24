import YM.FVA2.Extras.Pole
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
open Job.Belt Rake.Geo O.Hue O.Fuse O.Cool
variable {I:Type}{G:Gauge}{b d:ℤ}{r k n:ℕ}{B:Deck G}{K:Booked B}{M:MS_Data G K}
variable {P:Geo I} {F A:Glade G I}{X Y Z:T (Glade G I)}
/-! Exterior words in the MS computation. `Scriven` below requires them to have `Field ... 0`;
central mark (any k as in `Scriven.oneF`) is inserted last in `merge`. Each ext insertion has its own site. -/
abbrev Cart (G:Gauge)(I:Type):= (I→QP) × T (Glade G I)
def merge (G:Gauge)(I:Type) : List (Cart G I) → Cart G I→T (Glade G I)
| [],a=> swing G a.1 a.2
| b::l,a=> bond G I ( swing G b.1 b.2 ) (merge G I l a)
variable {P:Geo I}{F:Cart G I}{X Y:T (Glade G I)}{v e: Cart G I}{L: List (Cart G I)}
def Apart (P:Geo I)(v e:Cart G I): Prop:= CoverSep P (v.1-e.1)
def Field (P:Geo I)(M:MS_Data G K)(v:Cart G I)(k:ℤ): Prop:= Response v.2 M P.η k ∧ Cool.Fixed v.1 ∧ ∀ n, Known P (v.2 n)
structure Scriven (P:Geo I)(M: MS_Data G K)(v:Cart G I)(L:List (Cart G I))(k:ℤ) : Prop where
    oneF : Field P M v k
    others : ∀ i∈L, Field P M i 0
    apart : ∀ i∈ L,Apart P i v
    among : List.Pairwise (Apart P) L
namespace Scriven
lemma tail (h:Scriven P M v (e::L) b): Scriven P M v L b:= ⟨ h.oneF, fun i hi=> h.others i (List.mem_cons_of_mem _ hi),fun i hi=> h.apart i (List.mem_cons_of_mem _ hi),( List.pairwise_cons.mp h.among).2 ⟩
lemma head (H:Scriven P M v (e::L) b) : Field P M e 0:= H.others e (by simp)
lemma throughout (h:Scriven P M v (e::L) b) : (∀ i∈L, Apart P e i) ∧ Apart P e v:= ⟨( List.pairwise_cons.mp h.among ).1,h.apart e (by simp)⟩
end Scriven
lemma spinC (hv: Field P M v b): Banks ( swing G v.1 v.2 ) b ∧ Stageable P (swing G v.1 v.2) := ⟨( snakeV hv.1 ).life, fun _=>untitled ( royalU ( hv.2.2 _ ) ) hv.2.1 ⟩
lemma merge_now (h:Scriven P M v L b) : Banks ( merge G I L v ) b∧ Stageable P ( merge G I L v ) := by
    induction L with| nil=> exact spinC h.oneF| cons i L IH=> obtain ⟨hp,hv⟩:= spinC h.head; obtain ⟨hx,hX⟩:= IH ( Scriven.tail h ); exact ⟨ (zero_add b) ▸ joins hp hx, castW hv hX ⟩
lemma contacts (he:P.θ=0)(hm:Field P M e 0)(hv:Field P M v b)(hx:Apart P e v) : let U:= swing G e.1 e.2; let V:= swing G v.1 v.2; Sweep P (Share G I U V)∧ Sweep P (Serve.Touch G I U V) := by
    intro U V; constructor <;> ( intro n; (first | rw [Share, paired] | rw [ Serve.Touch,paired ]); refine Nilp.sum _ ?_; intro i _; unfold U V )
    · simp only [ swing,promised ]; rw [ attach ( hm.1.life _ ) ( hv.1.life _ ) ]; exact ( regionA he hx ( hm.2.2 _ ) ( hv.2.2 _ ) ).fixed hv.2.1
    exact touchN he hx hv.2.1 ( hm.1.life _ ) ( hv.1.life _ ) ( hm.2.2 _ ) ( hv.2.2 _ )
lemma aversion (he:P.θ=0)(h:Scriven P M v L b)(hp:Field P M e 0)(ht:Apart P e v)(hx:∀ i∈L,Apart P e i) : let U:= swing G e.1 e.2; let V:= merge G I L v; Sweep P (Share G I U V) ∧ Sweep P ( Serve.Touch G I U V ) := by
    intro U V; induction L with
    | nil=> exact contacts he hp h.oneF ht
    | cons i L IH=>
       -- V let generalized? change
       obtain hv:=Scriven.tail h; obtain ⟨hV,hZ⟩:= IH hv (fun j hj=> hx j (List.mem_cons_of_mem _ hj)); obtain ⟨hA,hX⟩:=spinC h.head; -- shadow hx
       obtain ⟨h1,h2⟩:= contacts ( e:=e ) ( v:=i ) he hp h.head (hx i (by simp)); obtain ⟨a,b⟩:= merge_now hv; -- name b
       obtain hu:= hedge ( spinC hp|>.1 ); constructor; · rw [ show V=bond G I ( swing G i.1 i.2 ) (merge G I L v) from rfl, share_graft hu (hedge hA) a ]; exact ( Sweep.ljoint h1 b ).add ( Sweep.rjoint hX hV )
       rw [ show V=bond G I ( swing G i.1 i.2 ) (merge G I L v) from rfl,touch_graft hu (hedge hA) a ]; exact ( Sweep.ljoint h2 b ).add ( Sweep.rjoint hX hZ )
lemma approx (he:P.θ=0)(h:Scriven P M v L b) : let X:= merge G I L v; ∃ Y:T (Glade G I), Banks Y b∧Sweep P Y∧∀ i,Velocity (X i) ((helm M P.η X-Y) i):= by
    intro X; induction L with
    | nil=> refine ⟨0,(fun _=> Bank.zero),Sweep.unit,?_⟩; rw [sub_zero]; exact ( snakeV h.oneF.1 ).vital
    | cons i L IH=>
       obtain ⟨Y,hY,hQ,H⟩:= IH ( Scriven.tail h ); obtain ⟨ha,hb⟩:= spinC h.head; obtain ⟨hx,ht⟩:= merge_now (Scriven.tail h); let A:= swing G i.1 i.2; let V:= merge G I L v; let S:=Share G I A V; let W:= bond G I A Y; have hA : Banks S b:= fun n=>Bank.all_fin (antidiagonal n) fun i _=> stretch ( ha i.1 ) ( hx i.2 );
       refine ⟨ W+S,( fun i=> ((zero_add b) ▸ joins ha hY i: Bank ( W i ) b ).add ( hA i ) ), Sweep.add ( Sweep.rjoint hb hQ ) (( aversion he (Scriven.tail h) h.head h.throughout.2 h.throughout.1 ).1), fun n=>?_ ⟩;
       change Velocity (bond G I A V n) ((helm M P.η (bond G I A V)-(W+S)) n); rw [ helm_charge (X:=A) (hedge ha) ]; obtain hW:= cruise ( snakeV (p:=i.1) h.head.1 ).vital H n; change Velocity _ ((bond G I (helm M P.η A) V + bond G I A (helm M P.η V - Y)) n) at hW; unfold W S; rw [ show bond G I (helm M P.η A) V+ _ + _- (_+_)=_ from (show _=bond G I (helm M P.η A) V+bond G I A (helm M P.η V-Y) from by rw [ map_sub ]; abel ) ]; exact hW
lemma script (he:P.θ=0)(h:Scriven P M v L b) : ∃ Y:T ( Glade G I ), Lucent P M b Y ( merge G I L v ):= by obtain ⟨p,H,hP,hK⟩:= approx he h; exact form_ψ he ( merge_now h |>.1 ) H hP hK
end YM.FVA2.Extras
