import YM.MS.Image.Verdant
/-!
# Recover highest rank(s) explicitly, without Wilson gauge

Used at order one bulk or order-zero mark. use cost from step serializer. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Outlook
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain Tone.Frame Momentum
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}{X Y F:T (Flats G)}{J N:Flats G}{b:Bool}{t r v:ℤ}{n m h:ℕ}{s y:ℝ}{K:Mob G}{f p:Coat G}{g q:T (Coat G)}
lemma joint_static (h:Count f n)(he:Live f): Joint n 0 (Finsupp.single 0 f) f 0:= by
    refine ⟨ vibe_root h,?_,Weighted.single (mer.uLive he) 0,(cone G).zero_mem, mer.zero, (fun _=>Home.zero _),?_⟩; intro t s; rw [pureP _ h]; exact he; rw [add_zero]; exact sip_root h
lemma core_base (hx: Joint n (0+step0 G J) J f p)(he:ClockD b t r J)(hf:Cap0 b t v f)(ht:Count f n)(hl: Live f):∃ V:Flats G, ClockD b t (v-2) V ∧Stay n V∧ Pact J (Finsupp.single 0 f+V):= by
    let P:Flats G:=Finsupp.single 0 f; have hu:= joint_static ht hl; have hp:=Cap0.heap.single hf 0; obtain ⟨V,p,hM,hV,hr⟩:=factory (mine (F:=P) hp hu.toll) (f:=0) (fun _=>Home.zero _) Cap0.zero; refine ⟨_,hV,hM.toll,( super (Y:=P+V) (q:=p) hx ?_ (show Pact 0 0 from fun _=> EventuallyEq.rfl) (f:=f) (g:=f) EventuallyEq.rfl he ( Cap0.heap.plus hp (clockTrans hV (show v-2≤v by omega)))).1⟩ -- Assert args wrong. hM type? 
    simpa only [ add_zero,zero_add,map_add] using hu.plus hM
lemma constant_base (hv: Home K n)(hp: kPrice K)(he:Cap0 b t r (fun _:ℂ=>K))(hB: Joint n (0+step0 G J) J (fun _:ℂ=>K) p)(hD:ClockD b t v J): Issue (r-2) (hereZ n J s y-K):= by
    obtain ⟨V,hV,ht,hS⟩:= core_base hB hD he (fun _=> hv) (Live.stays hp); have hT:= Lift.add ( Lift.stays hp) (live0 (s:=s) (y:=y) ht); have hx:= Train.prom hS n s y;
    rw [page_add, pureP _ (h:=fun _=>hv)] at hx; have he': hereZ n J s y=K+hereZ n V s y:= Lift.unique (live0 hB.toll) (Lift.congr hT hx.symm); rw [he',add_comm K,add_sub_cancel_right]; exact valueC ht ( Moony.toast ( clockMoon hV )) _ need_tail ( clockCap hV )
-- with schema ready `Leader`. need point static cohom.P
lemma bias {P:Mob G} {u:ℤ}(h:Issue u P)(hf: Fine b t (fun _:ℂ=>P)): Cap0 b t u (fun _:ℂ=>P):= ⟨hf, Eventually.of_forall fun _=>h⟩
-- corollaries leading
variable {U V:T (Mob G)}
lemma give (hs:Badge b (fun _:ℂ=>K) h t): kPrice K ∧ Home K h ∧ Fine b t (fun _=>K):= by obtain ⟨r,he⟩:= hs.stock; obtain ⟨a,hr⟩:= he.fine.tune.mer.price.exists; exact ⟨ hr,hs.born 0,he.fine⟩
lemma HB (hx:leader G X (gloss U) q)(hc: Badge true (gloss U 1) 4 0)(hv:Issue r (U 1)) : Issue (r-2) (NumX s y 4 X 1 - U 1):= by
   obtain ⟨p,Ht,hV,hL⟩:= (hx 1).1; obtain ⟨hu,hC,h⟩ := give (K:=U 1) hc; rw [show program G 1 X=0 from ?_] at Ht; exact constant_base hC hu (bias hv h) Ht hV; unfold program; rw [ show shortB 1=∅ by ext t; simp [ shortB ]; omega]; simp
lemma HM (hx:comet h t X (gloss V) F g)(hc: Badge false (gloss V 0) h t)(hv: Issue r ( V 0)) : Issue (r-2) (NumX s y h F 0- V 0):= by
   obtain ⟨v,he,hf,hQ⟩:= (hx 0).1; obtain ⟨hp,hU,hW⟩:= give (K:=V 0) hc; rw [show platform X 0 F=0 from ?_] at he; exact constant_base hU hp (bias hv hW) he hf; unfold platform shortM; simp
end YM.MS.Outlook
