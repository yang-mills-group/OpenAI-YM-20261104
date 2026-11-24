import YM.MS.Echo.Refresh
/-!
Estimates on a single insertion's linearized orbit. We bring exact bounds to all lengths `>=1`,
(natural frequency 1/R), to apply to the BV Laplacian, not assuming control of gauges on
residual modes. Stage log μZ=logν.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Echo
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Native Fiddle
open Lattice Book Convolve Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Flux City Signal Modeled Frame Wire Latch Job Belt Rake Orbit Orbit.LogReal Vista High.Knobs Fleet
open scoped Topology ContDiff Interval
variable {G:Gauge}{n i k:ℕ}{ φ: Actor G}{u v:ℤ}{X F:Dec G}{p:Team}{R: High.Recount G}
variable (x:ℝ)
def bud : Visa Unit := ⟨ fun _=>1+|x|,fun _=>by simp ⟩
local notation "Ξ"=> unbounded (bud x)
abbrev SpanT:= Set.Ici (1:ℝ)
def sp (p:SpanT): ( unbounded (bud x) ).time := ⟨ (), Real.log (1+p.val), show 0 ≤ Real.log (1+p.val) from Real.log_nonneg (by linarith [ Set.mem_Ici.mp p.property ])⟩
abbrev rel:= borrow (unbounded (bud x)).price (sp x)
lemma τz (p: SpanT): Vista.τ ( Belt.tstart (sp x p) ) = p.val:= by change exp ( log (1+p.val))-1=p.val; rw [ exp_log (show 0<1+p.val from (by linarith [Set.mem_Ici.mp p.property ]))]; ring
lemma future (p:SpanT): (rel x).length p=p.val:= by change Vista.lamp ( Belt.tstart _ )=_; unfold Vista.lamp; rw [τz x p]; exact max_eq_right p.property
lemma hf (p:SpanT): (rel x).basic p=(1+|x|)*(1+ log (1+p.val)):= by change _*(1+ |log _|)=_; rw [ abs_of_nonneg ( Real.log_nonneg (show 1 ≤ 1+p.val by linarith [Set.mem_Ici.mp p.property])) ]; rfl
lemma soon (p:SpanT): 1≤(rel x).length p:= future x p ▸ p.property
lemma ηv : SpaceOut.warmV (fun _=>x) (bud x):= fun _=>le_rfl
abbrev keeping (Q:Wind.Pack G): SpanT→ Law G:= fun p=> Q x p.val
variable {E I:Type}[ NormedAddCommGroup E ][NormedSpace ℝ E] {S:Scale I}
lemma hint_comp (w:Wire ( BH G ) E QP )(h:∀ i,1≤ S.length i): Bound S ( fun _ p=>hook weightψ (sail w p) ) 1:= by
    induction w with| nil=> exact Costs.scalar (p:=fun _=>(1:ℂ)) ( Cost.of_le fun _ _ _=> by simp )| cons i l ih=>
       rcases i with ⟨i,L⟩; let P:= Tone.offset i.1; have he(p:E): weightψ (i,L p)= Tone.bill P ( L p ):= Tone.rights ..; have ht: paid S (fun _=>‖P‖) S.length:= ⟨ ‖P‖+1,(by positivity),0,fun i=> by rw [pow_zero,mul_one]; apply le_trans _ (le_mul_of_one_le_right ( show 0≤‖P‖+1 by positivity ) (h i )); linarith ⟩
       simp only [ hook,List.map_cons, sail_cons,List.prod_cons,he ]; exact pulse_bill L ih ( paid_at ht (fun i=> S.pos i|>.le))
variable {b:Bool} {d:ℝ}
lemma νtransfer {Q:Wind.Pack G}(h:WarpHere b true Ξ ( Ext G Q (fun (_:Unit)=> x) ) (goodM Ξ d)): Lease b true ( rel x ) ( keeping x Q ) ((goodM Ξ d)∘ sp x):= by
    let f(p:SpanT):= sp x p; let F (y:SpanT):= actorP Ξ ( Ext G Q (fun (_:Unit)=>x)) ( sp x y ); intro E _ _ w hx hw; obtain he :Cape (rel x) F (( goodM Ξ d )∘ f) w:= Job.ticket ( Z:=(Ξ).price ) ( w:=fun i=>Qbud w (Ξ).price (goodM Ξ d) i ) ( P:=f ) ⟨ ⟨ 1,zero_lt_one,1,fun i=>by rw [pow_one,one_mul,Pi.one_apply,mul_one]; rfl ⟩,1,zero_lt_one,fun i=>by rw [ one_mul ]; rfl⟩ (h E w hx hw) ( paidMono ( fun i=> le_rfl ) ) ( pos_nn _ (fun i=> pay_m Ξ d _) _ )
    have hg(p:SpanT):sleeve weightψ ( F p )=Q x p.val:= by unfold F actorP; change sleeve weightψ ( sleeve lace ( Q x (Vista.τ _) ))=_; rw [τz x p]; ext; simp_rw [sleeve_here,← mul_assoc, hook_c,one_mul]
    unfold Cape at *; convert ( Costs.mul ( hint_comp w ( soon x ) ) he ) using 1; · ext p v; unfold Plane.Chart keeping; rw [← hg p]; rfl -- may hg hidden keeping
    ext; simp [f]
variable (B: Fixed ( col ( skyline G p )) R true 4 1)(K:Circle G φ false u)(H:PM φ ( skyline G p ) F u)
include B K H
def ratioF (y:SpanT) := goodM Ξ eps_gain ( sp x y )
lemma mantle : Lease false true ( rel x ) ( keeping x ( F n ) ) (ratioF x):= by
   let N (_:Unit):=walkway 0; let Q(_:UnitW):=φ; let W:= ( bud x ); let U:= TokenB G p (fun (_:Unit)=> x); let A:= goalsK (fun (_:UnitW) (_:Unit)=> 0) (fun _=> x) Q; have hp: SpaceOut.FlowSet W A:= moneyM (fun (_:UnitW) (_:Unit)=>0) ⟨ ηv x,fun _=> ⟨‖Tone.embed 0‖+1,(by positivity),0,fun i=> (by rw [pow_zero,mul_one,Pi.one_apply,mul_one]; exact le_of_lt (lt_add_one ..)) ⟩⟩ (fun _=>⟨ _,_,K⟩)
   obtain ⟨ X,Y,V,hV⟩:= Orbit.LogReal.CorΦ ( K:= Orbit.uniform G Unit ) (outside N) 0 (healthy ..) ( tokenCaps p (fun (_:Unit)=> x) G ) (fun i=> (hp i).1); have hB:=soloB hV.action (dawnG (fun _=> x) N (skyPC G p)); let Z?:= SpaceOut.Doors G W N; obtain hc := ζ_cover hV ( show Vista.Gate W X A from ⟨ by rw [hB]; exact SpaceOut.sky_budget (ηv x) (skyPC G p) B,fun i=>(hp i).2 ⟩ ) Z?; have hx:Crew (outside N) _ _ _ _ A V:=hV.crew; rw [ hB, deadD rfl hV.defect ] at hx; have he:= hc.1 Ξtag ( Finset.singleton_nonempty _ ) n; rw [ δclock H hx ] at he; exact νtransfer x he
end YM.MS.Echo
