import YM.MS.Puff.Forest
import YM.MS.Milk.Mural
import YM.MS.Milk.Outfit
import YM.Next.RANK.GaussTags
/-!
# Multi-standard.Even connected equation only.Expose operations.Near past estimate when all distinct, theorem.Probewise identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Milk
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Analysis Submodule InnerProductSpace City Next.Rank Next.Rank.Normal Theater Drops Maxwell Local.Physical
open Labels
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {A X W:Type}{G:Gauge} [LinearOrder W]{n d r:ℕ}{s:ℝ}{U:W→ℝ}{P:W→Pol G}
local infix:70 " ⋆ "=> product (field Landau.parity)
local notation "Φκ"=> field (P:=QP) ( Landau.parity ( C:=G.ColorIndex ) ( A:=Axis ) )
open Puff SplitP Puff.Log Engine Dynamics Actors Swirl
abbrev ASeq (G: Gauge): Actors (OM (Lane4 G)):= roof ℝ ( Breeze.Shine G )
local notation "uK"=> marked W
abbrev band (G:Gauge): Dynamics ( ASeq G ):={ (HeatFlow.deriv ( field Landau.parity)) with valid:=Status } -- derives?
lemma onlyD (F H V:OM (Lane4 G))(hp:Status F H)(hv:Status F V): H=V:= funext fun i=> funext fun w=> (hp.path i w).unique (hv.path i w)
abbrev Season (G:Gauge): Engine ( ASeq G ):= Puff.Station ℝ (Move G)
lemma lead_born {E:Type}[AddCommGroup E][Module ℂ E](M:Actors E)(x:W)(F:Finset W→ E): Meter M ( marked W ) F {x}=F {x}:= by
    rw [ spawn ]; have he : (uK).grade {x}=1:= Finset.card_singleton x; have hm : ∑ i∈restS uK {x}, M.core ( α uK i.1 • Meter M uK F i.1 ) ( F i.2 )=0:= by
       refine Finset.sum_eq_zero fun t ht=>?_ ; obtain hv: α uK t.1=0:= by have h:=keep uK ht; unfold α; exact_mod_cast (show (uK).grade t.1=0 from Nat.eq_zero_of_le_zero (by omega));
       rw [hv,zero_smul,map_zero,LinearMap.zero_apply]
    rw [issue,hm,cloak uK]; simp [α,he]
variable (x:W→E4) (hx: Injective x) (f:W→Pol G)
abbrev MeterU (s:Finset W): OM (Lane4 G):= arc (pot s f) (Forum G x) ( Taxi G x hx )
abbrev Meter0 (s:Finset W): OM (Lane4 G):= arc (pot s f) (Forum G x) (fun t=> Normal.self fun (_:W)=> Bend G t)
abbrev LogU : Finset W→ OM (Lane4 G):= Meter (ASeq G) uK ( MeterU x hx f )
lemma zeroU : MeterU x hx f ∅ = (ASeq G).unit := funext fun s=> show Tint _ _ 1=_ from Milk.step0 _
lemma ExpU : Cheer (ASeq G) uK (LogU x hx f)= MeterU x hx f:= Log.solve (ASeq G) uK _ ( zeroU x hx f ) (fun _ x hx'=> fills _ _)
lemma pureU (s:Finset W)(t:ℝ): LogU x hx f s t∈ Roof G:= MeterIN (ASeq G) uK (MeterU x hx f) (ASeq G).guard (ASeq G).close (fun _ t _=> fills _ _ ) s t (Set.mem_univ _)
lemma onlyE (p:W)(s:ℝ): LogU x hx f {p} s=arc (f p) ( RawS G (out (x p)) ) ( Bend G ) s:= by rw [LogU, lead_born,MeterU,pot,Finset.prod_singleton ]; exact standardμ ..
lemma originL : LogU x hx f ∅=0:= Log.happy (ASeq G) uK _
abbrev Ink (G:Gauge):= ( Season G ).join
lemma motion (p:Finset W) : Status (LogU x hx f p) ( Wrap ( LogU x hx f p )+∑ i∈ picks p,Ink G ( LogU x hx f i ) ( LogU x hx f ( p\i ) ) ):= by
    let V:= LogU x hx f; let U:= MeterU x hx f; let D:=Season G
    obtain hm: Status (V p) ( D.move (V p) + (2:ℂ)⁻¹ • ((uK).Lift D.join V V p)):= Log.Reverse uK D ( band G ) onlyD ( y:=U ) ( fun i=> Milk.Lift (stayT x hx (G:=G)) _ ) ( zeroU x hx f ) ((universe0 _).mpr fun i t _=> fills _ _ ) p
    rw [Stencil.halfB D.join _ (by intro i j; exact D.rear (fun j _=>pureU x hx f i j) (fun i _=>pureU x hx f j i)) ( originL x hx f ) ] at hm; exact hm
-- self recursion direct. Need rank.Log not important
-- removed
-- already!
local notation "Nκ"=> Meter0 x f
abbrev soloA (x:W→E4)(v:W→Pol G)(i:W):= arc (v i) (RawS G (out (x i))) (Bend G)
def Sent (x:W→E4)(f:W→ Pol G)(p:Finset W):= if h:p.Nonempty ∧ p.card=1 then soloA x f ( p.min' h.1 ) else 0
lemma sent_u (p:W): Sent x f {p}=soloA x f p:= by simp [ Sent ]
lemma sent_e (p:Finset W)(hp:p.card≠1): Sent x f p=0:= by simp [Sent,hp]
lemma readyH : Cheer (ASeq G) uK ( Sent x f )=Meter0 x f:= by
    funext s; induction s using Finset.induction with
    | empty => have hp: Happy uK ( Sent x f ):= sent_e x f ∅ (by simp); rw [show (∅:Finset W)=(uK).origin from rfl, Stencil.simple_E _ _ _ hp ]; funext s; exact (show Tint _ _ 1 = _ from Milk.step0 _ )|>.symm -- 1 type
    | insert i s hi ih=>
       rw [Stencil.cheers _ _ _ _ _ hi, ih, sent_u ]; exact funext fun v=>(solo_H x i s f hi v)|>.symm; swap; · exact sent_e x f;
       intro p s _; unfold Sent; split; exact fills _ _; exact (Roof G).zero_mem -- order placeholders
lemma restG : Meter (ASeq G) uK Nκ=Sent x f:= by
    rw [← readyH ]; apply recheck (ASeq G) uK ( t:= _ ); · intro p _; unfold Sent; split; exact fun v _=> fills _ _; exact (ASeq G).guard.zero_mem
    exact sent_e x f ∅ (by simp)
-- Capsule next.
end YM.MS.Milk
