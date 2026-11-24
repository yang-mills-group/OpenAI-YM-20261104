import YM.FVA2.Extras.Bond
import YM.FVA2.O.Rough.Peak
/-! # The `nav` part drops out (`silence`) on the public exteriors

Auxiliary to `YM/FVA2/Extras/Result.lean`. -/
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
variable {P:Geo I}{U:Cart G I}{Z W Y:T (Glade G I)} {v: I→QP}{L:List (Cart G I)}
def publicW (P:Geo I)(M:MS_Data G K)(L:List (Cart G I)): Prop:= ∀ i∈ L, Certified i.2 M P.η 0
lemma silent_m (H: P.θ=0)(hp: Scriven P M U L b)(he: publicW P M L): Sweep P ( nav M P.η (merge G I L U)-merge G I L ( U.1,nav M P.η U.2) ):= by
    induction L with
    | nil=> have ht := nax (M:=M) (η:=P.η) (p:=U.1) (fun n=> ( hp.oneF.1.life n ).cross ); simp only [ merge,ht,sub_self ]; exact Sweep.unit
    | cons i s IH=>
       obtain hl:= Scriven.tail hp
       obtain hT:= IH hl ( fun j hj=> he j ( List.mem_cons_of_mem i hj ) )
       let Y:= swing G i.1 i.2; obtain ⟨hP,hV⟩:= spinC hp.head; obtain hv: nav M P.η Y=0:= (snake ( he _ (by simp))).2
       let X:= merge G I s U; let Z:= merge G I s ( U.1,nav M P.η U.2 ); change Sweep P ( nav M P.η (bond G I Y X)-bond G I Y Z ); rw [ nav_charge (hedge hP),hv,map_zero, LinearMap.zero_apply,zero_add, add_comm, add_sub_assoc,← map_sub ]; exact ( aversion H hl hp.head hp.throughout.2 hp.throughout.1 |>.2 ).add ( Sweep.rjoint hV hT )
lemma herein (H:P.θ=0)(hp: Scriven P M U L b)(he: publicW P M L)(hm:Lucent P M b Z (merge G I L U)): Lucent P M (b+1) ( nav M P.η Z ) ( merge G I L (U.1,nav M P.η U.2) ) := by
    refine ⟨hm.1.ward.1,?_⟩; let W:=merge G I L U; let X:=merge G I L ( U.1,nav M P.η U.2 ); change Sweep P ( nav M P.η Z-X ); have ht:= merge_now hp |>.1; have hx:Sweep P ( nav M P.η (Z-W) ):= fun n=> Nilp.navs hm.2 ( fun i=>( (hm.1.life i ).sub (ht i)).cross ) _; rw [show nav M P.η Z=nav M P.η (Z-W)+nav M P.η W from by rw [map_sub,sub_add_cancel], add_sub_assoc ]; exact hx.add ( silent_m H hp he )
lemma silence (H:P.θ=0)(hp: Scriven P M U L b)(he:publicW P M L)(hK:Lucent P M (b+1) Y ( merge G I L ( U.1, nav M P.η U.2 ) ) )(p:I)(n:ℕ): blade ( Y n ) p=0:= by obtain ⟨Z,hZ⟩:= script H hp; rw [unique_resp hK ( herein H hp he hZ ) ]; exact closeQ hZ.1 p n
end YM.FVA2.Extras
