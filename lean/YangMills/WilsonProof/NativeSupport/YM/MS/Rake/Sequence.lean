import YM.MS.Rake.Sequence
import YM.MS.Rake.Res
/-!
# Real data families for infinite lattice & continuum scheme, lamp assumptions gathered.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo Land Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W] {G:Gauge}{ P: Geo I}{B:Local.Physical.Deck G}{O:Land.Booked B}{M: Land.MS_Data G O}
-- each label arbitrary owner. no null output.Control.B.Leg uses 1 measure
variable (V:LitBook B) (P:Geo I)(T: Prescription B)(M: Land.MS_Data G O)
def initials (P:Geo I)(T: Prescription B):= circle P.η (col (skyline G T.team)) -- B inferred from T
-- bug global G.M.
def approach (P:Geo I)(M:MS_Data G O): Site G I := circle P.η ( Archive 4 M.bulk )
def rowK (x:Label B): Site G I:= circle P.η (col ( horizon V T.team ( T.fees x.h x.item ) ))
def rowM (x:Label B): Site G I:= circle P.η ( Archive x.h (M.marks x.h x.item))
lemma VeniceD (x:Label B) : Ven (fun _=>planeF) (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (approach P M) (rowM P M x):= by
    -- namespace order P V? inspect. road not full? use roadM
    let K:= M.marks x.h x.item; let H:= Archive x.h K; let T:= M.markOK x.h x.item; intro n; refine ⟨ nameD_warm ( Emit.Host.host (gang ( T n )) ),?_⟩; intro i w t; obtain h := pour (spaceD G) ( Outlook.roadM M.bulkOK T ) (P.η i) w n t; rw [ ergo ( η:=P.η )] at h; exact h
lemma lightL (h:G.Simple)(x:Label B) : Ven (fun _=>planeF) (constantP G I (LowP G)) (constantP G I (PlanetL G)) ( initials P T ) ( rowK V P T x ) := by
    let B:=skyline G T.team; let A:= T.fees x.h x.item; let H:= horizon V T.team A; obtain hP:= Marked.law (Wind.mark_seek V (d:=x.h) (p:=T.team) h) A; let Q:=Wind.Seek V T.team x.h;
    have hG:= hP.road; change Domain.Flow _ _ _ _ _ (Wind.col H) at hG; have hh (i:ℕ):Wind.Fees false 0 (H i):= ( Wind.aqua V T.team A ).owes i; intro n; refine ⟨ nameWarm (H n) (hh n),fun i w t=>?_ ⟩; obtain hv := pour (spaceL G) hG (P.η i) w n t; rw [ ergo (η:=P.η) ] at hv; let z:=exp t; let f:= H n (P.η i); have he : sailP (fun _=>μzone) (constantP G I (LowP G)) (rowK V P T x n) i t=cycle (PlanetL G t) planeF (f z):= ( startCycle f 0 (hh n|>.stay (P.η i)) _ _ ).symm
    rw [ show sailP (fun _=>(spaceL G).measure) _ (circle _ (col H) n) i t= _ from he ] at hv; exact hv
lemma tagD (k:ℕ): Tip P false true 4 ( approach P M k ):= by obtain h := Host.host (gang ( M.bulkOK k )); exact ⟨ collectD h, nameD_warm h,sund P _ h ⟩
lemma tagL (k:ℕ): Tip P true true 4 (initials P T k):= by obtain h: Fees true 0 _:= (skyPC G T.team).owes k; exact ⟨collectFee h,nameWarm _ h, Lease.sticks (sunX P _ h) (fun i=> rank_e P i 4)⟩
lemma tagF (x:Label B)(k:ℕ): Tip P false false x.h (rowM P M x k):= by obtain h:=Host.host (gang ( M.markOK x.h x.item k )); exact ⟨collectD h, nameD_warm h,sund P _ h⟩
lemma tagX (x: Label B)(k:ℕ): Tip P true false x.h (rowK V P T x k):= by obtain h: Fees false 0 _:= ( Wind.aqua V T.team ( T.fees x.h x.item ) ).owes k; exact ⟨collectFee h,nameWarm _ h, Lease.sticks (sunX P _ h) (fun i=> rank_e P i x.h) ⟩
-- main stamps from Knobs.Fixed
structure Tour (K L: Planet G I)(P:Geo I)(x:Position W I) (b:Bool)(Y:Site G I)(H: W→ Site G I)(sizes:W→ℕ): Prop where
    plot: Mesh P x
    ground: Stage K L P b
    energy i : 0< i → Tip P b true 4 ( Y i )
    obey i n: Tip P b false (sizes i) (H i n)
    register s: Ven (fun _=> planeF ) K L Y (H s)
variable {P}{x:Position W I} (R: Mesh P x) (labels:W→ Label B) -- declare x
include R
omit [LinearOrder W] in
lemma tourist (hc:G.Simple) : Tour ( constantP G I (LowP G) ) (constantP G I (PlanetL G)) P x true (initials P T) (rowK V P T ∘ labels) (Label.h ∘ labels):= ⟨ R,Geo.masterL .., fun _ _=> tagL P T _, fun i n=> tagX V P T (labels i) n,fun s=> lightL V P T hc (labels s) ⟩
omit [LinearOrder W] in
lemma builder : Tour (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) P x false (approach P M) (rowM P M ∘ labels) (Label.h ∘ labels):= ⟨ R,Geo.masterD .., fun _ _=> tagD P M _, fun i n=>tagF P M (labels i) n,fun i=>VeniceD P M ( labels i ) ⟩
end YM.MS.Rake
