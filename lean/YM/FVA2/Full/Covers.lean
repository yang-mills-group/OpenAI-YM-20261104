import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
import YM.MS.Rake.Edict
import YM.MS.Vane.Trigger
import YM.FVA2.Full.Costs
/-! FVA_2 addition: `FullBook` with W-type shifts.
Module Covers. Relevant proofs extended from `LitBook` in
YM.MS.Rake.Sequence
YM.MS.Rake.Edict
YM.MS.Vane.Trigger.
Main stencils/rank/affordability modified in `YM.FVA2.Full.Glyph`.
Names with `F` suffix are generally for the adjusted versions.
No changes to `PhysicalSum`, BV prescription or `MS_Data`. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo Land Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W] {G:Gauge}{ P: Geo I}{B:Local.Physical.Deck G}{O:Land.Booked B}{M: Land.MS_Data G O}
variable (V:FullBook B) (P:Geo I)(T: Prescription B)(M: Land.MS_Data G O)
def rowKF (x:Label B): Site G I:= circle P.η (col ( horizonF V T.team ( T.fees x.h x.item ) ))
lemma lightLF (h:G.Simple)(x:Label B) : Ven (fun _=>planeF) (constantP G I (LowP G)) (constantP G I (PlanetL G)) ( initials P T ) ( rowKF V P T x ) := by
    let B:=skyline G T.team; let A:= T.fees x.h x.item; let H:= horizonF V T.team A; obtain hP:= Marked.law (Wind.mark_seekF V (d:=x.h) (p:=T.team) h) A; let Q:=Wind.SeekF V T.team x.h;
    have hG:= hP.road; change Domain.Flow _ _ _ _ _ (Wind.col H) at hG; have hh (i:ℕ):Wind.Fees false 0 (H i):= ( Wind.aquaF V T.team A ).owes i; intro n; refine ⟨ nameWarm (H n) (hh n),fun i w t=>?_ ⟩; obtain hv := pour (spaceL G) hG (P.η i) w n t; rw [ ergo (η:=P.η) ] at hv; let z:=exp t; let f:= H n (P.η i); have he : sailP (fun _=>μzone) (constantP G I (LowP G)) (rowKF V P T x n) i t=cycle (PlanetL G t) planeF (f z):= ( startCycle f 0 (hh n|>.stay (P.η i)) _ _ ).symm
    rw [ show sailP (fun _=>(spaceL G).measure) _ (circle _ (col H) n) i t= _ from he ] at hv; exact hv
lemma tagXF (x: Label B)(k:ℕ): Tip P true false x.h (rowKF V P T x k):= by obtain h: Fees false 0 _:= ( Wind.aquaF V T.team ( T.fees x.h x.item ) ).owes k; exact ⟨collectFee h,nameWarm _ h, Lease.sticks (sunX P _ h) (fun i=> rank_e P i x.h) ⟩
variable {P}{x:Position W I} (R: Mesh P x) (labels:W→ Label B)
include R
omit [LinearOrder W] in
lemma touristF (hc:G.Simple) : Tour ( constantP G I (LowP G) ) (constantP G I (PlanetL G)) P x true (initials P T) (rowKF V P T ∘ labels) (Label.h ∘ labels):= ⟨ R,Geo.masterL .., fun _ _=> tagL P T _, fun i n=> tagXF V P T (labels i) n,fun s=> lightLF V P T hc (labels s) ⟩
end YM.MS.Rake
end
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo Land Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program
open scoped Topology ContDiff Interval
variable {I W:Type}{G:Gauge}{P:Geo I}{K:Belt I}
   {Fp Q: Recount G}{u v:ℤ}
variable {B: Local.Physical.Deck G}(V:FullBook B){O:Booked B}(M:MS_Data G O)(T:Prescription B)(p:W→ Label B)
lemma offersF (h: TaylorOKF M V T)(hv: Gold P K): Arch K (constantP G I (LowP G)) ( constantP G I (PlanetL G) ) (initials P T) ( rowKF V P T∘ p ) ( Label.h∘ p ) ∧ Arch K (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (approach P M) (rowM P M ∘p) (Label.h∘p) ∧ ArcS K (constantP G I (LowP G)) (constantP G I (PlanetL G)) (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (initials P T) (approach P M) ( rowKF V P T ∘p ) (rowM P M ∘ p) ( Label.h ∘ p ):= by
    let S:= K.price; have hb (n:ℕ)(he: 0< n):= partials hv ( show 1 ≤ n from he ) ( fun r hr=> h.bulk n he r hr );
    have H (i:W) (n:ℕ) := partials hv ( show 0≤ n from Nat.zero_le n ) ( fun r hr=> (h.mark ( p i|>.h ) (p i|>.item)) n ( Nat.zero_le _ ) r hr );
    have he i : 1≤K.price.length i:= hv.day i ▸ Real.one_le_exp ( hv.paid i ); have hx:= cost_D (G:=G) hv.day
    exact ⟨ ⟨CoupleY he hv.day,Mate0 he hv.day,fun i hi=>(hb i hi).1,fun i n=>( H i n).1⟩, ⟨fun i j=> polar (hx i j),hx,fun i hi=>(hb i hi).2.1,fun i n=> (H i n).2.1⟩, ⟨ submarineT he hv.day (phaseY hv),submarineP he hv.day (phaseY hv), fun i hi=> ( hb i hi).2.2, fun i n=>(H i n).2.2 ⟩ ⟩
end YM.MS.Rake
end
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge}{P:Geo I}{K:Belt I}{F H D: Glade G I}{X:I→ℂ}{d h:ℕ}{ζ:ℝ}
variable { J:Type}[LinearOrder W]{x:Position W I}{c b:Bool}{K L K' L':Planet G I}{B B': Site G I}{A A':W→Site G I}{R:W→ℕ}{p:ℝ}{U V:Dance G I W}{S:Finset W}{v:I→ℝ}
local notation "m0"=> (fun (_:I)=>planeF)
open Land Pearl Train Booked Menus Local.Physical
variable { B: Deck G} (V:FullBook B){O:Booked B}(M:MS_Data G O)(T:Prescription B)(R:W→Label B)(P:Geo I)
abbrev LOrdF (V: FullBook B)(P:Geo I)(T:Prescription B)(R: W→Label B)(x:Position W I)(U:Dance G I W):= Fields x m0 (constantP G I ( LowP G )) ( constantP G I ( PlanetL G )) (initials P T) ( rowKF V P T ∘ R ) U
include T
lemma CoversF (h:G.Simple)(hx: Mesh P x)(he:TaylorOKF M V T): ∃ U V', LOrdF V P T R x U ∧ DOrd O P M R x V' ∧ ∀ S: Finset W,S.Nonempty→ ∀ n:ℕ,let k:= charge ( Label.h∘ R ) S; Verdict P k 0 ( U S n ) ∧ Verdict P k 0 ( V' S n ) ∧ Verdict P k eps_gain ( U S n - V' S n ):= by
    obtain ht:= touristF V T hx R h; obtain hV:= builder M hx R; obtain ⟨ U,hU⟩:= formal ht; obtain ⟨W,hW⟩:= formal hV; obtain ⟨Z,X,Tz⟩:= offersF V M T R he (gulfG (P:=P)); obtain ⟨Y,Q,RQ⟩:= offersF V M T R he ( westV (P:=P) ); exact ⟨ U,W,hU,hW,fun _ hp n=> ⟨ closure ht Z Y hU hp n, closure hV X Q hW hp n,trade ht hV Z X Y Q Tz RQ hU hW hp n⟩ ⟩
end YM.MS.Vane
end
