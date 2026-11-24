import YM.FVA2.O.Dust.Aroma
/-!
# From the past boundary: pricing the Ward terms

`tContext`: calculate that `nav` applied to the full product is rapidly decaying
at negative infinite time. `Point` will turn this into the exact Ward condition (at all times).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Cool
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Osc MS.Osc.Snap MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real MS.Tide
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane Actors Fuse Job.Belt
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}{F H:Glade G I}{a b:I→QP}{P:Geo I}{B:Deck G}{K:Booked B}{M:MS_Data G K}{Y X:Rake.Dance G I W}{q:ℤ} {x: Position W I}{U:W→Rake.Label B}{S:Finset W}
local notation "Qx"=> (east P false)
local notation "BΩ"=> (fun _ : I=> lineB G)
local notation "m0"=> (fun _ : I=>planeF)
lemma hug (hp:Bank F 0)(ht:Bank H q): voyage BΩ true (Serve.tilt G a F) ( Serve.tilt G b H )= Serve.tilt G b (regionC m0 (a-b) BΩ F H) := funext fun i=> funext fun t=> tension (U:=lineB G t) rB (reverse_b G t 0) (cl_b G t 0) hp.invoice ht.invoice (Ward.truthP (hp.tone i t)) (a i) (b i)
lemma touchN (hs:P.θ=0)(hx:CoverSep P (a-b))(h:Fixed b)(hp:Bank F 0)(ht:Bank H q)(he:Known P F)(hu:Known P H): Nilp P (voyage BΩ true (Serve.tilt G a F) (Serve.tilt G b H)):= by rw [ hug hp ht ]; obtain ⟨u,hv⟩:=he; obtain ⟨q,hq⟩:=hu; exact ( region_P hs χB hx hv hq ).fixed h
variable [LinearOrder W] (hM:Mesh P x)(ht:P.θ=0)(hx:DOrd K P M U x X)(h:∀ i,Fixed (x i))
include hM hx
lemma us (S:Finset W): Banks (untap x X S) 0:= fun i=> bankTilt ( solitude hx ( world_price hM hx ) i )
include ht h
lemma becoming (S:Finset W)(k:W)(he:k∉ S): Sweep P (Serve.Touch G I (untap x X {k}) (resin x X S )):= by
    induction S using Finset.induction_on with
    | empty=> rw [ resin_nil, Toe ( us hM hx _) ]; exact Sweep.unit
    | insert i s hi IH=>
        let V:=untap x X; let B:=resin x X s; rw [ resin,raw_wax (us hM hx) hi,touch_graft (hedge (us hM hx _)) (hedge (us hM hx _)) ( eating (fun s=> wax_guard (us hM hx) s)) ]; refine Sweep.add ( Sweep.ljoint ?_ ( aroma hM ht hx h s ) ) ( Sweep.rjoint ( gustS hM ht hx h ) (IH fun p=>he (mem_insert_of_mem p)) ); rw [headU hx,headU hx]; intro n; rw [Serve.Touch,paired]; apply Nilp.sum; intro y h'; let M0(u:W):=Response.visit ( M:=M ) (η:=P.η) ( U u |>.item ); exact touchN ht ( hM k i (fun p=> he ( p ▸ mem_insert_self .. )) ) ( h i ) ( M0 k|>.life y.1 ) ( M0 i|>.life y.2 ) ⟨_,safeM (U k)⟩ ⟨ _,safeM (U i) ⟩
lemma notice (s:Finset W): Sweep P (nav M P.η ( resin x X s )):= by
    induction s using Finset.induction_on with
    | empty=> rw [resin_nil,gazeU]; exact Sweep.unit
    | insert i s hi ih=>
       let p:= untap x X; have hz : nav M P.η (p {i})=0:= by unfold p; rw [ headU hx ]; exact ( snake ( Certified.first (M:=M) (η:=P.η) ((U i).item) ) ).2
       rw [resin,raw_wax (us hM hx) hi, nav_charge (hedge (us hM hx _)),hz,map_zero,LinearMap.zero_apply,zero_add ]; exact ( Sweep.rjoint ( gustS hM ht hx h ) ih ).add ( becoming hM ht hx h s i hi )
lemma tContext : Sweep P (nav M P.η ( plenum x X S )) := by
    let V:= plenum x X S; let L:= resin x X S
    have he := (plenum_R hx (world_price hM hx) S).life; have hv:Banks L 0:= eating (fun s=> wax_guard (us hM hx) s); have hp := sents hM ht hx h S; suffices ht : Sweep P (nav M P.η (V-L)+nav M P.η L) by rw [← map_add,sub_add_cancel] at ht; exact ht
    exact Sweep.add (x:=nav M P.η (V-L)) (fun i=> Nilp.navs hp (fun i=> ( Bank.sub ( he i ) (hv i)).cross ) i ) (notice hM ht hx h S)
end YM.FVA2.O.Cool
