import YM.MS.Vista.CashZ
/-!
# Consolidated estimates.Hypothesis Meter credit to realize later. Both orbit+plain finite in one.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo Orbit.LogReal
open scoped Topology ContDiff Interval
variable {I W E:Type}[LinearOrder W]{G:Gauge}{L:I→Side}{b:Bool}
   {X Y:Rake.Site G I}{ Z: Lin I}{V:Visa I}{P K:Planet G I}{D D':H_defect G I}
   {M N:Rake.Dance G I W}{T:Finset W}{n:ℕ}{Q:ℕ→I→ Law G}{Q':Seeds G I W}{A:I→Cover}
local notation "Ξ"=> Mid V L
local notation "Ν"=> Ap Ξ (tickA L)
local notation "Ṽ"=>unbounded V
local notation "Z'"=> outside L
local notation "Μ"=>μF Ξ L
local notation "Ϝ"=>enterV L b
local notation "Ρ"=>After V L
abbrev Tail (V:Visa I)(L:I→Side)(p:(After V L).time):= exp (-eps_gain * ( tstart p-until0 L p.1 ))
lemma tail_h (V:Visa I)(L:I→Side): nn (Tail V L):= fun _=> exp_pos _|>.le
lemma tail_m : Tail V L≤1:= fun p=> by apply exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p_gain.le) ( sub_nonneg.mpr ( afterT p ))
structure Budget (V:Visa I)(L:I→Side)(K P:Planet G I) : Prop where
    fix : Glow K -- K finite mesh ext Δ after; P cover.
    logw : Glow P
    meet : Piece ( Mid V L ) K 1
    hook : Piece (After V L) K (Tail V L)
    head: Piece ( unbounded V ) P 1
    twin: stepOne V L K P
-- place independent of V later prove from horizontal geometry.
def Width (P:Belt I)(u:I→Side)(Z:Lin I)(X:I→Cover): Prop:= (∀ j:Half, TPaid P ( μF P u ) ( Ap P (tickA u) ) ( loci Z j ) X ) ∧ (∀ i j:Half,i≠j→TPaid P (μF P u) ( Ap P ( tickA u ) ) (loci Z i) (loci Z j))
structure Place (V:Visa I)(L:I→ Side)(b:Bool)(A:I→Cover) : Prop where
    mind: Width (Mid V L) L (enterV L b) A
    after: Width (After V L) L ( enterV L b ) A
    center: RepT V L A
structure Gate (V:Visa I)(X:Rake.Site G I)(Q':Seeds G I W): Prop where
    tower : bulk ( unbounded V ) X
    mark (S: Finset W)(n:ℕ) : Lease false true ( arrival V ) ( Q' S n ) 1 -- rank≥1.Later extra assumption rank0 for endpoint?
variable (hS:Circuit ( outside L ) P Q A Q' X D M)(hS': Circuit (enterV L b) K Q A Q' Y D' N)
    (hx: Gate V X Q')(H:Budget V L K P)(hz:Place V L b A)
def Balk (V:Visa I)(Z:Lin I)(K:Planet G I)(X:Rake.Site G I)(D:H_defect G I)(A: Faces I)(F: Rake.Dance G I W): Prop:= marketS (unbounded V) F ∧ ∀ n j,j.Nonempty→ HandC false false ( unbounded V ) ( fort Z A K X D F j n ) ( Beef ( unbounded V ) )
-- Price includes scalar difference and all mark upper
structure Period (P:Belt I)(Ω:Lin I)(L:Planet G I)(B:Rake.Site G I)(D:H_defect G I)(M:Rake.Dance G I W)(A:Faces I)(c:P.time→ℝ): Prop where
    tower : bulk P B
    ends : Cushion P D
    outputs : marketS P M
    usd (n:ℕ)(T:Finset W)(he:T.Nonempty): HandC false false P ( fort Ω A L B D M T n ) (c*Beef P)
include hx hS
omit hS [LinearOrder W] in
lemma cap_B : bulk Ξ X:= fun n hn=> (by obtain h:= hx.tower n hn; unfold χr WarpHere at h ⊢; rw [ ← good_η ] at h ⊢; exact cup_to_v h) -- hS omit
omit hS hx in
lemma wokeMark {P:Belt I}{K:Planet G I}(hf:Crew Z K X D A Q' M)(hP: Market P V 0)(he:∀ i,P.price.length (castdown hP i)=1)(hv:Lease false true (arrival V) (Q' T n) 1)(ht:T.Nonempty) : Lease false true P.price ( LaunchF P 0 (warp0 G I ( M T n )) ) ( Beef P ):= by
   refine awake _ _ hP he ( PaceF 0 hP.acc ) ?_; rw [show (fun i:I=> warp0 G I ( M T n ) i 0) =_ from ?_]; exact hv; exact funext fun i=> Eq.trans (congr_arg ( M T n i ) τ0) ( hf.2 T ht n|>.1 i )
include H
lemma ζ_cover : Balk V Z' P X D A M:= by
   have hx0: Presence Ṽ Z' (fun _=>planeF) D A:= Or.inl (deadD rfl hS.defect); have hm: Vel Ṽ Z' P (fun _=>planeF) 1:= ⟨ routineQ (Ṽ).price,H.head,fun _=>zero_le_one⟩; have hi: marketS Ṽ M:= fun S hs n=> cabinet hS H.logw hx.tower hx0 hm ontoM.acc (fun i hi n=> wokeMark hS.crew ontoM (by intro i; change lamp 0=1; rw [Vista.lamp,τ0,max_eq_left zero_le_one]) ( hx.mark i n) hi ) hs n; refine ⟨ hi,fun i S hs=>?_⟩; have hv:= drive_budget hS hx.tower hx0 hm hi hs i; rw [one_mul] at hv; exact hv -- order a?? explicit patch
include hS' hz
abbrev δM (P:Belt I)(L:I→Side):= Ap P (tickA L)
lemma μ_maker : Period Ξ Ϝ K Y D' N A 1:= by
   let P' := Mid V L
   have hm:= M_vel (b:=b) H.meet
   have hB:bulk Ξ Y:= fun i hi=> ( Mundane ⟨ H.fix,hS'.action,hS'.finances ⟩ ⟨ H.logw,hS.action,hS.finances⟩ H.meet ( cap_B hx ) H.twin hi ).1
   have hD:Cushion Ξ D':= D_gen H.fix hS'.defect hS'.finances hS'.fund hm hB nextM.acc (fun i j hj=> no_credit 0 ( fun i=> zero_le_one ) (fun x=> by rw [Pi.zero_apply,τ0]; exact (hS'.defect i).2 j hj |>.1 x)) hz.mind.2; -- origin.Have proof
   have hv: Presence Ξ Ϝ Μ D' A := Or.inr ⟨ hD,Ν,hz.mind.1 ⟩; have hM: marketS Ξ N:= fun S hs n=> cabinet hS' H.fix hB hv hm nextM.acc (fun i hi k=> wokeMark hS'.crew nextM (by intro i; change lamp 0=1; rw [Vista.lamp,τ0,max_eq_left zero_le_one]) ( hx.mark i k ) hi ) hs n; exact ⟨hB,hD,hM,fun k T hs=> drive_budget hS' hB hv hm hM hs k⟩
lemma last_m : Period Ρ Ϝ K Y D' N A ( Tail V L ):= by
    obtain ⟨h,hX,hN,_⟩:= μ_maker hS hS' hx H hz; obtain he:= Next_fee (b:=b) H.hook (tail_h _ _); have hb:= Vel.up he tail_m; have h0:bulk Ρ Y:= Large_B hb h ⟨ H.fix, hS'.action, hS'.finances⟩; have hD:Cushion Ρ D':= D_gen H.fix hS'.defect hS'.finances hS'.fund hb h0 soonM.acc (fun i j hj=> by have he(P:Belt I): goodM P 0=1:= (by ext; simp [goodM]); apply ( he Ρ ) ▸ ( Vista.station (h:= ?_) (hp:= unit_span ( d:=0 )) ); rw [ he ]; exact hX i j hj  ) hz.after.2; have hf: Presence Ρ Ϝ (μF Ρ L) D' A:=Or.inr ⟨ hD,δM Ρ L,hz.after.1⟩; have hM: marketS Ρ N:= fun S hs n=> cabinet hS' H.fix h0 hf hb soonM.acc (fun i hi k=> Vista.station (hN i hi k) unit_span ) hs n; exact ⟨ h0,hD,hM,fun n S hs=> drive_budget hS' h0 hf he hM hs n⟩
-- final comparison abstract
lemma Peak (ht:T.Nonempty)(i:ℕ): ΔMark V L false ( N T i-M T i ) := by
   obtain he:= cap_B hx; obtain ⟨hB,hD,hM,_⟩:= μ_maker hS hS' hx H hz; have hy(S:Finset W)(hs:S.Nonempty)(n:ℕ): MarkT Ξ ( M S n ):= cup_to_v ( ζ_cover hS hx H |>.1 S hs n ); exact O_motion hS' hS H.meet H.twin hB ( fun i hi=> Mundane ( show Core Ϝ K Y Q from ⟨ H.fix,hS'.action,hS'.finances ⟩ ) ⟨ H.logw,hS.action,hS.finances ⟩ H.meet he H.twin hi|>.2 ) hD hM hy hz.mind.1 hz.center ht H.fix H.logw i
end YM.MS.Vista
