import YM.FVA2.O.Seam.Boom
/-!
# Before matching (log times up to θ): force the off-diagonal estimates

`thicket_gap`: starts with pointwise (not a uniform cost) for the boundary condition
`PastPoint`. Other hypotheses include uniform separation of the two groups. Propagates to `Chaff`
uniform over the parameter space. Forcing priced via `fieldV` (see `O/Seam/Boom`).
`core_nav`: related estimate on commuting the attachment of the far fields with the
continuum Ward differential (needed e.g. for an odd second slot).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo O.Price O.Fuse
open scoped Topology ContDiff Interval
variable { G: Gauge }{ α W Z I : Type }{B: Deck G}{K: Booked B}{M:MS_Data G K}{P:Geo I}{S:Home α I}{ F H X:T ( Glade G I )}{a:I→ QP}{u:ℤ}{n:ℕ} {r:Label B}
abbrev Burst (S:Home α I)(P: Geo I)(M:MS_Data G K)(X:T ( Glade G I )) := ∃ F:T ( Glade G I ), Chaff S P F ∧ ∀ n,Velocity ( X n ) ( (F+helm M P.η X) n )
lemma Burst.from_R (h:Response X M P.η u): Burst S P M X:= ⟨0,Chaff.zeros,by rw [zero_add]; exact h.vital ⟩
lemma Burst.fork (h:liveP S P.η)(hv:Burst S P M X)(he:Chaff S P ( Share G I ( singletonM P M a r ) X )): Burst S P M (bond G I ( singletonM P M a r ) X):= by
    let F:= singletonM P M a r; obtain ⟨Y,hp,hv⟩:=hv; have hX : Response F M P.η 0:= (Certified_single _).1; refine ⟨ bond G I F Y-Share G I F X,(Chaff.pass ( priceT h ) hp).minus he,?_⟩; rw [helm_charge (hedge hX.life), sub_add_eq_add_sub, ← add_assoc, add_sub_cancel_right, add_left_comm (bond G I F Y)]; intro n; obtain hh:= cruise hX.vital hv n; rw [ map_add ] at hh; exact hh
lemma Burst.sub (h:Burst S P M X)(he:Burst S P M H): Burst S P M (X-H):= by
    obtain ⟨F,hF,hV⟩:= h; obtain ⟨Y,hY,hE⟩:= he; refine ⟨F-Y,hF.minus hY,?_⟩; rw [ map_sub, show F-Y+(helm M P.η X-helm M P.η H)=(F+helm M P.η X)-(Y+helm M P.η H) from (by abel) ]; intro i; exact Velocity.sub ( hV i ) (hE i)
lemma Burst.keep (h:Banks X u)(he:Burst (deckB P) P M X)(hr:∀ i,PastPoint ( X i )): Chaff (deckB P) P X := by obtain ⟨F,hP,hU⟩:=he; exact fun i=> synchronized.mp ( ahead ( Y:=F ) ( M:=M ) (fun i=> (h i).heat ) (fun i=> (h i).cross ) hU hr (fun i=>synchronized.mpr (hP i)) i )
variable [LinearOrder W]{x:Position W I} {s:Finset W}{R: W→Label B}
local notation "S0"=> deckB P
lemma burstF (hp:Mesh P x)(he:Response H M P.η u)(ht:Calm S0 P H)(hx:∀ i∈s, Chaff S0 P ( Share G I ( singletonM P M ( x i ) ( R i ) ) H )): Burst S0 P M ( rootT P M x R s H ) := by
    induction s using Finset.induction_on with
    | empty=> rw [R_nil]; exact Burst.from_R he
    | insert i s hi ih=> rw [ R_step ( mesh_sep hp ) i hi ]; apply Burst.fork early_live ( ih fun j hj=> hx j (mem_insert_of_mem hj) ) ( shareProbe Belt_grass early_live (mesh_sep hp) ht he.life ( fun j hj=> hp i j (fun p=>hi (p ▸ hj)) ) (hx i (by simp)) ) -- apply
lemma drift (hp:Mesh P x)(he:Response H M P.η u)(hX:Response X M P.η u)(ht: Calm S0 P H)(hx:∀ i∈s,Chaff S0 P ( Share G I ( singletonM P M ( x i ) ( R i ) ) H ))(hr:∀ i,PastPoint ( ( X-rootT P M x R s H ) i )): Chaff S0 P ( X-rootT P M x R s H ) := Burst.keep ( fun i=> Bank.sub ( hX.life i ) (R_bank ( mesh_sep hp ) he.life _ i) ) ( Burst.sub ( Burst.from_R hX ) ( burstF hp he ht hx ) ) hr
variable (hp: Mesh P x)(ht: ∀ i:W,CoverSep P ( x i ))
-- early cost for cluster from D. assume past; discharged in `O/Seam/Coat`
variable [LinearOrder Z]{y:Position Z I}{U: Z→Label B}{p:Finset Z}{r:Label B}
include hp ht
lemma thicket_gap (hv: Mesh (flatten P) y)(hb:∀ i,Cool.Fixed ( y i ))(hX:Response X M P.η 0)(hx:∀ i∈s,∀ j∈p,CoverSep P ( x i-y j ))(hr:∀ i,PastPoint ( ( X-rootT P M x R s ( thicket P M y U p ) ) i )): Chaff S0 P ( X-rootT P M x R s ( thicket P M y U p ) ) := drift hp ( firm ( mesh_sep hv )|>.1 ) hX ( thicket_T hv hb ) ( fun i hi=> fieldV hv hb (ht i) ( hx i hi ) ) hr
lemma single_gap (hX:Response X M P.η 0)(hr:∀ i,PastPoint ( ( X-rootT P M x R s ( rowM P M r ) ) i )): Chaff S0 P ( X-rootT P M x R s ( rowM P M r ) ) := drift hp ( Response.visit r.item ) hX (fun _=> Earn ( Lend.heart early_live )) (fun i _=> ShareE Belt_grass early_live ( ht i ) ( Response.visit r.item |>.life ) (fun _=> Lend.heart early_live)) hr
local notation "M0"=> Mid P
lemma core_nav (he:Reps H 0 ( Station P ))(hB:Banks H u): Chaff M0 P (nav M P.η ( rootT P M x R s H )-rootT P M x R s (nav M P.η H)) := by
    induction s using Finset.induction_on with
    | empty=> rw [R_nil,R_nil,sub_self]; exact Chaff.zeros
    | insert i s hi ih=>
        let F:=singletonM P M ( x i ) ( R i ); let Y:= rootT P M x R s H; let Z:=rootT P M x R s ( nav M P.η H ); have hf: Certified F M P.η 0:= Certified_single _; rw [ R_step ( mesh_sep hp ) i hi,R_step (mesh_sep hp) i hi ]; change Chaff _ P ( nav M P.η ( bond G I F Y )- bond G I F Z ); rw [ nav_charge (hedge hf.1.life),hf.2,map_zero,LinearMap.zero_apply,zero_add, add_sub_right_comm, ← map_sub ]; exact (Chaff.pass ( priceT Mid.live ) ih).add ( touchProbe Mid.grass Mid.live (mesh_sep hp) (fun i=> Earn ( zero_reps he i )) hB ( fun j hj=> hp i j (fun p=> hi (p ▸ hj)) ) ( TouchE Mid.grass Mid.live ( ht i ) hB ( zero_reps he ) ) )
end YM.FVA2.O.Seam
