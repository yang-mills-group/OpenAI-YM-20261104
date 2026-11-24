import YM.ForFlash.MS.Rake
import YM.MS.Vane.Akin
import YM.MS.Vane.Peel
/-! Adapted from the YM modules indicated. Only lower gap hypothesis on the Mesh arguments,
see Phase for the change in the estimate itself. -/
set_option autoImplicit false
noncomputable section

/- Widening MS/Vane/Rocket -/
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I E J:Type}{G:Gauge}[LinearOrder J] {s:Finset J}{P:Geo I}{R: J→ℕ}{x:Position J I}{K L:Planet G I}{b:Bool} {X H: Site G I}{A:J→Site G I}{Y:Dance G I J}{n:ℕ}{μ:I→Measure QP}
variable (h:TourForFlash K L P x b X A R)(hv: Fields x (fun _=>planeF) K L X A Y)
local notation "m0"=> (fun (_:I)=>planeF)
include h
lemma formalForFlash : ∃ Y, Fields x m0 K L X A Y:= by obtain ⟨Y,h,H⟩:= nominalForFlash h.ground h.plot h.energy ( fun i n=>⟨_,h.obey i n⟩ ); exact ⟨_,h⟩
include hv
lemma emergedForFlash (hp:2≤s.card)(n:ℕ): Came P b (Y s n):= by obtain ⟨U,hx,hL⟩:= nominalForFlash h.ground h.plot h.energy ( fun i n=>⟨_,h.obey i n⟩ ); rw [perfect hv hx]; exact hL s hp n
lemma tip0ForFlash (hs:s.Nonempty): ∃ a:ℕ,Tip P b false a ( Y s n ):= by
    by_cases he: s.card ≥ 2; · exact ⟨0,tipby (emergedForFlash h hv he n) _ ⟩;
    obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp ( show s.card=1 from by obtain he':= Finset.card_pos.mpr hs; omega ); rw [hv.2.1]; exact ⟨_,h.obey i n⟩
lemma foundedForFlash (hp:s.Nonempty)(n:ℕ): collect ( Y s n ) ∧ Warm ( Y s n ) false:= by obtain ⟨v,hm⟩:= tip0ForFlash h hv (n:=n) hp; exact ⟨hm.1,hm.2.1⟩
lemma hospForFlash (hp:s.Nonempty)(n:ℕ): Warm ( Src x m0 K L X Y s n ) false:= by
    refine CabinF.warm_zip ( warm_sum (F:=fun i=> expJ _ _ _) _ (fun i hi=>?_)) (warm_sum _ (fun i hi=>warm_sum _ (fun j hj=>?_)))
    · exact walk_tree h.ground.pinC ( h.energy ( n-i ) (by obtain hx: i<n:= ( Finset.mem_Ico.mp hi ).2; omega)|>.2.1 ) ( foundedForFlash h hv hp i |>.2 )
    exact warmJoin (fun _=>Coherent) h.ground.pool (foundedForFlash h hv ( n_small hi |>.2.1 ) _ |>.2 ) ( foundedForFlash h hv ( n_small hi|>.2.2.1 ) _|>.2 )
lemma winterForFlash (hp:s.Nonempty)(n:ℕ): Warm (rhs x m0 K L X Y s n) false:= CabinF.warm_zip ( warmCycle (fun _=> Coherent) h.ground.pool ( foundedForFlash h hv hp n|>.2 )) ( hospForFlash h hv hp n )
lemma motionForFlash (hp:s.Nonempty)(n:ℕ) : Fits false ( Y s n ) (rhs x m0 K L X Y s n):= by
    obtain hh:= winterForFlash h hv hp n; refine ⟨ hh.walk, ?_⟩; intro i w hw t; by_cases hx:s.card<2
    · obtain ⟨k,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from by obtain he:= Finset.card_pos.mpr hp; omega); have hc: picks ({k}:Finset J)=∅:= Finset.eq_empty_iff_forall_notMem.mpr fun i hi=> clips (by simp) hi; unfold rhs Src multi; rw [hc,hv.2.1]; rw [Finset.sum_empty,add_zero]; exact h.register k n |>.motion i w t
    let H:=rhs x m0 K L X Y s n; obtain ⟨hu,hW,hM⟩:= hv.2.2 s (le_of_not_gt hx) n; change Y s n=river H at hM; have hx:(fun t:ℝ=> Y s n i t w)=fun t:ℝ=> river H i 0 w+∫ s in 0..t,H i s w:= funext fun t=> by rw [hM]; exact swamp hW i t 0 hw
    rw [hx]; exact ( hfun (hh.walk _ _ hw) t ).const_add _
end YM.MS.Vane

/- Widening MS/Vane/Bee -/
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I E W:Type}{G:Gauge}{P:Geo I}{x E':ℝ} {b:Bool}{F H:Glade G I}{X: I→QP}{Y:Recount G}{n k l h:ℕ}[DecidableEq W]{s:Finset W}
 {K L:Planet G I}
local notation "℧"=> Gulf P
lemma lightingForFlash (hs:Sheet (℧).price 1 (plug L))(hx:CoverSepForFlash P X)(hp:Here false true ℧ F (rateS ℧ n))(he:Here false true ℧ H ( rateS ℧ k )) : Bud P (n+k) 0 (regionC (fun _=>planeF) X L F H):= by
    intro j; obtain ⟨a,ha,hA⟩:= hx.floor; refine Lease.sticks ( PulseQForFlash (v:=fun i=>P.roots i.1) (A:=X ∘ Sigma.fst) hs hp he (fun _=>zero_le_one) ( rateC _ _ ) (rateC _ _ ) ha (fun _=>exp_pos _) (fun i=> hA i.1) (fun i=> le_trans ( le_of_eq ( near i ) ) ( exp_monotone ( authority i|>.2 ))) j ) ?_; intro i; rw [dotzero, dotzero, roll, Pi.one_apply,one_mul, ← stock,zero_add, add_zero, Nat.zero_add];
end YM.MS.Vane

/- Widening MS/Vane/Peel -/
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I E J:Type}{G: Gauge}[ LinearOrder J ]{s:Finset J}{P:Geo I}{R: J→ℕ}{x:Position J I}
 {K L: Planet G I} {b:Bool} {X: Site G I}{A:J→Site G I}{Y: Dance G I J}{n k d:ℕ}{F H: Glade G I}{μ:I→Measure QP}
local notation "Ϋ"=> Gulf P
local notation "m0"=> (fun (_:I)=>planeF)
variable (h: TourForFlash K L P x b X A R)(hx: Fields x (fun _=>planeF) K L X A Y)(hu:Arch ( Gulf P ) K L X A R)
include h hu
lemma germSForFlash (_hp:2≤s.card)(n:ℕ)(hv:∀ t⊂ s,t.Nonempty→∀ i,Here false false Ϋ ( Y t i ) ( rateS Ϋ ( charge R t )))(hK:∀ i<n,Bud P (charge R s) 0 (Y s i)): Bud P (charge R s) 0 (Src x (fun _=>planeF) K L X Y s n):= by
    intro k; refine Lease.plus ?l ?r
    · exact He_here (K:=Gulf P) (Domain.paths n 0) (fun i hi=> ( shines Ϋ hu.main ( hu.states (n-i) (by obtain hp: i<n:= ( Finset.mem_Ico.mp hi ).2; omega)) (( hK i ( Finset.mem_Ico.mp hi|>.2 ) k ).highp) (raised P 0 (charge R s) k) )) ( raised _ _ _ _ )
    ·
      refine He_here (K:=Gulf P) _ (fun i hi=> He_here (K:=Gulf P) _ (fun k hk=> ?_) ( raised _ _ _ _ )) ( raised _ _ _ _ )
      obtain ⟨ Q,hg,H,hJ⟩:= n_small hi; rw [← toll_charge R Q.le]; exact lightingForFlash hu.χ ( Rake.spaceForFlash h.plot hi ) ((hv i Q hg k.1).highp) (( hv _ hJ H k.2 ).highp) _
include hx
lemma moonForFlash (hs:s.Nonempty)(n:ℕ): Here false false Ϋ ( Y s n ) ( rateS Ϋ (charge R s) ) ∧ ( s.card≥2→ Bud P (charge R s) 0 ( Y s n )) := by
    induction s using Finset.strongInductionOn generalizing n with| _ s ih=>
       by_cases hp:s.card≥2; swap; · obtain ⟨k,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from by obtain hx:= Finset.card_pos.mpr hs; omega); refine ⟨?_,fun h=>False.elim (hp h)⟩; rw [hx.2.1]; simpa only [charge,Finset.sum_singleton] using hu.first k n
       induction n using Nat.strong_induction_on with | h n hM=>
          suffices he: Bud P (charge R s) 0 ( Y s n ) from ⟨ more he,fun _=> he⟩; intro k; let F:= Y s n; let H:= Src x (fun _=>planeF) K L X Y s n; let Q:=charge R s; let N:=k+Q+1; let V:=Gulf P; let p:= life P Q N 0; have he:= Fits.positiveR (P:=P) (motionForFlash h hx hs n); have hU:= emergedForFlash h hx hp n; have hi : 0<( N-Q-(0:ℝ) ):= by unfold N; push_cast; linarith
          have hc:Bud P Q 0 H:= germSForFlash h hu hp n (fun t ht hs n=> (ih t ht hs n).1) (fun i hi=> (hM i hi).2 hp );
          apply Lease.sticks (S:=V.price) (f:=plug F) _ (tilt (P:=P) ( x:=0 ) ( h:=Q ) (show k≤ N from by unfold N; omega)); refine marching (εGulf P) ( raised _ _ _ _ ) ( winterForFlash h hx hs n|>.walk ) he ( Midland hi.le b ( hU.1.pick N )) ( aboveC V false hU.2 ) ?_
          intro r hr hF E _ _ _ w hw ht; obtain ⟨ε,hε,hS⟩:= fertile (P:=P) hi E w ht (fun h=> Bool.noConfusion h); have hW := penny hF ( raised _ _ _ _) hu.χ ( fun i=> zero_le_one ) (Tall V.price 5 (by omega)) (fun E _=> tom V.price 5 (by omega) ); rw [one_mul] at hW; exact ⟨_,_,hε, Lens.plus hW ( pinch ( hc N ) hr ) E w hw ht, hS⟩
end YM.MS.Vane

/- Widening MS/Vane/Houses -/
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W: Type}{G:Gauge}{P: Geo I}{S:Belt I}{x:ℝ}{K L K' L': Planet G I} {b c:Bool}{F H X Y:Glade G I}
 {ξ:I→QP} {d r k:ℕ}
local notation "Ϋ"=> Gulf P
lemma RiverForFlash {a b c:Stem P→ℝ}(hc: CoverSepForFlash P ξ)(he: Flow Ϋ K a)(hg: Here false true Ϋ F b)(hv: Here false true Ϋ H c)(ht:nn a)(hm:nn b)(hN:nn c)(l:ℕ): Here false false Ϋ ( regionC (fun _=>planeF) ξ K F H ) ( fun p=>a p*(b p*c p) * ( ( Gulf P ).price.length p / P.roots p.1 ) ^ l ) := by obtain ⟨C,hC,hW⟩:= hc.floor; apply PulseQForFlash (A:=fun p=> ξ p.1) he hg hv ht hm hN hC (fun p=> exp_pos _) (fun i=> hW i.1) (qp_le)
lemma boatsForFlash (hc: CoverSepForFlash P ξ)(he:Flow Ϋ L 1)(hf: Flow Ϋ (L-L') (chips (Gulf P))) (hu: Here false true Ϋ F (rateS Ϋ d))(hH:Here false true Ϋ H ( rateS Ϋ d )) (hp: Here false true Ϋ ( F-H ) (chips Ϋ*rateS Ϋ d ))( hv: Here false true Ϋ Y (rateS Ϋ r))( ht: Here false true Ϋ ( X-Y ) (chips Ϋ*rateS Ϋ r)) (hw:Warm H false)(hw':Warm F false)(hV:Warm X false)(hV': Warm Y false)(hb: BackF L)(hh:BackF L'): Bud P (d+r) eps_gain ( regionC (fun _=>planeF) ξ L F X-regionC (fun _=>planeF) ξ L' H Y ) := by
   intro k; refine parkD hu hH hp hv ht hw hw' hV hV' hb hh (fun _=>Coherent) ?_ ?_ ?_; all_goals intro B T h1 h2
   · apply Lease.sticks (RiverForFlash hc he h1 h2 (fun _=>zero_le_one) (rateC _ _) (joy cul (rateC _ _)) k ); intro p; trans chips Ϋ p * life P (d+r) k 0 p; apply le_of_eq; rw [show k= (0:ℕ)+k from (by simp), stock 0, ← (by simpa using roll (P:=P) (x:=0) (η:=0) d r 0 0 p : life P d 0 0 p*life P r 0 0 p=life P (d+r) 0 0 p )]; try simp only [Pi.one_apply,Pi.mul_apply];
     rw [congr_fun (dotzero (P:=P) d) p, congr_fun (dotzero (P:=P) r) p,zero_add]; ring
     exact (congr_fun (alter P (d+r) k) p).ge
   · apply Lease.sticks (RiverForFlash hc he h1 h2 (fun _=>zero_le_one) (joy cul (rateC _ _)) (rateC _ _) k ); intro p; trans chips Ϋ p * life P (d+r) k 0 p; apply le_of_eq; rw [show k=(0:ℕ)+k from (by simp), stock 0, ← (by simpa using roll (P:=P) (x:=0) (η:=0) d r 0 0 p : life P d 0 0 p * life P r 0 0 p=life P (d+r) 0 0 p )]; try simp only [Pi.one_apply,Pi.mul_apply];
     rw [congr_fun (dotzero (P:=P) d) p, congr_fun (dotzero (P:=P) r) p,zero_add]; ring
     exact (congr_fun (alter P (d+r) k) p).ge
   apply Lease.sticks (RiverForFlash hc hf h1 h2 cul ( rateC _ _ ) ( rateC _ _ ) k); intro p; trans chips Ϋ p * life P (d+r) k 0 p; apply le_of_eq; rw [show k=(0:ℕ)+k from (by simp), stock 0, ← (by simpa using roll (P:=P) (x:=0) (η:=0) d r 0 0 p : life P d 0 0 p*life P r 0 0 p=life P (d+r) 0 0 p ) ]; 
   rw [congr_fun (dotzero (P:=P) d) p, congr_fun (dotzero (P:=P) r) p,zero_add]; ring
   exact (congr_fun (alter P (d+r) k) p).ge
end YM.MS.Vane

/- Widening MS/Vane/Akin -/
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge}[LinearOrder W] {P: Geo I}{x: Position W I}{R:W→ℕ}{K L K' L':Planet G I}{F H:Glade G I}
  {c b:Bool} {A B: Site G I}{X Y: W→ Site G I}{U V: Dance G I W}{n h:ℕ}
local notation "Ϋ"=> Gulf P

structure ChaseForFlash (P:Geo I) (x:Position W I) (μ: I→Measure QP)(R:W→ℕ)(b:Bool)(K L:Planet G I)(A:Site G I)(X: W→ Site G I)(U:Dance G I W): Prop where
   tour : TourForFlash K L P x b A X R
   fields : Fields x μ K L A X U
variable (T: ChaseForFlash P x (fun _=>planeF) R b K L A X U)(T': ChaseForFlash P x (fun _=>planeF) R c K' L' B Y V)(M: Arch (Gulf P) K L A X R)(N: Arch (Gulf P) K' L' B Y R)(J: ArcS (Gulf P) K L K' L' A B X Y R)
include T T' M N J
lemma tissueForFlash (S:Finset W)(n:ℕ)(hs:S.Nonempty)(hz:∀ v⊂ S,v.Nonempty→∀ k, Here false false Ϋ (U v k-V v k) (chips Ϋ*rateS Ϋ (charge R v)))(hf:∀ i<n,Bud P ( charge R S) eps_gain ( U S i-V S i ))(hp:2≤ S.card): Bud P (charge R S) eps_gain ( Src x (fun _=>planeF) K L A U S n - Src x (fun _=>planeF) K' L' B V S n ):= by
   let W0 i:= life P ( charge R S ) i eps_gain; intro k; unfold Src multi lonely; rw [ add_sub_add_comm,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]; apply Lease.plus
   · refine He_here (K:=Gulf P) _ (fun i hi=>?_) ( raised _ _ _ _ ); obtain he:i<n:= Finset.mem_Ico.mp hi |>.2; obtain hK : n-i>0:= by omega;
     have hv:= hf i he k; rw [ show life P _ k eps_gain =_ from alter P ( charge R S ) k ] at hv ⊢; exact Trees M.main J.main ( N.states _ hK ) ( M.states _ hK ) ( J.states _ hK ) ( ( (moonForFlash T'.tour T'.fields N hs i).2 hp k ).highp ) hv.highp ( raised _ _ _ _ ) cul
   · refine He_here ( K:=Gulf P ) _ (fun i hi=>?_) ( raised _ _ _ _ ); obtain ⟨H,hx,h,h'⟩:= n_small hi; rw [← Finset.sum_sub_distrib, ← toll_charge R H.le]; refine He_here (K:= Gulf P) _ ( fun j hj=>?_ ) ( raised _ _ _ _ );
     exact boatsForFlash (spaceForFlash T.tour.plot hi) M.χ J.χ ( (moonForFlash T.tour T.fields M hx j.1).1.highp ) ( ( moonForFlash T'.tour T'.fields N hx j.1).1.highp ) ( (hz _ H hx j.1).highp ) ( ( moonForFlash T'.tour T'.fields N h j.2).1.highp ) ( (hz _ h' h j.2).highp ) ( foundedForFlash T'.tour T'.fields hx _|>.2 ) (foundedForFlash T.tour T.fields hx _|>.2 ) ( foundedForFlash T.tour T.fields h _|>.2 ) ( foundedForFlash T'.tour T'.fields h _|>.2 ) T.tour.ground.pool T'.tour.ground.pool k
lemma tokensForFlash (S:Finset W)(n:ℕ)(hs:S.Nonempty): Here false false Ϋ ( U S n-V S n ) (chips Ϋ*rateS Ϋ (charge R S)) ∧ ( S.card≥2→ Bud P (charge R S) eps_gain ( U S n-V S n ) ) := by
   induction S using Finset.strongInductionOn generalizing n with| _ S ih=>
      by_cases hu:2≤ S.card; swap; · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show S.card=1 from by obtain he:= Finset.card_pos.mpr hs; omega); refine ⟨?_,fun h=>False.elim ( hu h )⟩; rw [ T.fields.2.1, T'.fields.2.1, mul_comm, charge, Finset.sum_singleton ]; exact J.first i n
      induction n using Nat.strong_induction_on with| h n hx=>
        suffices he: Bud P (charge R S) eps_gain ( U S n-V S n ) from ⟨ marketing he,fun _=> he⟩; intro k; let r:=charge R S; let ℓ:= k+r+1; have hK : 0<( ℓ-r-eps_gain:ℝ):= by change 0< (( (k+r+1:ℕ):ℝ) - _ - 1/2 ); push_cast; linarith
        let X0:= Src x (fun _=>planeF) K L A U S n; let Y0:= Src x (fun _=>planeF) K' L' B V S n; let F:= sailP (fun _=>planeF) L; let G:= sailP (fun _=>planeF) L'; let Jw:=U S n; let H:=V S n; let D:= Jw-H; let W:=( F Jw-G H )+(X0-Y0); obtain hx':Here false false Ϋ (X0-Y0) ( life P r ℓ eps_gain ) := tissueForFlash T T' M N J S n hs (fun i hi hp k=>( ih i hi k hp ).1) (fun j hj=>(hx j hj).2 hu ) hu ℓ;
        have hB: Fits false D W:= by unfold W; rw [← add_sub_add_comm]; exact Fits.subFit (motionForFlash T.tour T.fields hs n) (motionForFlash T'.tour T'.fields hs n);
        have hu' := emergedForFlash T.tour T.fields hu n; have hv:= emergedForFlash T'.tour T'.fields hu n;
        apply Lease.sticks (f:=plug D) _ (tilt (P:=P) ( m:=k) (n:=ℓ) (x:=eps_gain) ( h:=r ) (by unfold ℓ; omega)); refine marching (εGulf P) (raised _ _ _ _ ) hB.stroll ( Fits.positiveR hB ) ( Lease.minus (Midland hK.le b (hu'.1.pick ℓ)) (Midland hK.le c (hv.1.pick ℓ)) ) (aboveC Ϋ false ( combine hu'.2 hv.2 )) ?_; intro i hi hF E _ _ _ w hw ht; obtain ⟨ε,hε,hS⟩:= fertile (P:=P) hK E w ht (fun p=> Bool.noConfusion p); refine ⟨ _,_,hε, ?_,hS⟩;
        refine Lens.plus (F:=plug (F Jw-G H)) ?_ ( pinch hx' hi ) E w hw ht; rw [show life P r ℓ eps_gain= _ from alter P r ℓ] at *; exact LensD M.χ J.χ hF (pinch ( (moonForFlash T'.tour T'.fields N hs n).2 hu ℓ ) (fun x=> Bool.noConfusion x)) hu'.1.mood hv.1.mood T.tour.ground.pool T'.tour.ground.pool cul ( raised P 0 r ℓ )
end YM.MS.Vane
