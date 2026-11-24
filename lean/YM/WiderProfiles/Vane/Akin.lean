import YM.MS.Vane.Akin
import YM.WiderProfiles.Vane.Houses
import YM.WiderProfiles.Vane.Peel
/-!
WiderProfiles §F.1. Derivations extended from `YM/MS/Vane/Akin.lean`.
Upper growth consumes an exponent of the existing market in `WCoverSep.pay`,
used at the four purchase sites touch/lighting/River/placeW. The rest of this
family of `_wide` lemmas propagates that change, following the original proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge}[LinearOrder W] {P: Geo I}{x: Position W I}{R:W→ℕ}{K L K' L':Planet G I}{F H:Glade G I}
  {c b:Bool} {A B: Site G I}{X Y: W→ Site G I}{U V: Dance G I W}{n h:ℕ}
local notation "Ϋ"=> Gulf P
-- combine proof both.Now nested budgets.WTour & Arch.
structure WChase (P:Geo I) (x:Position W I) (μ: I→Measure QP)(R:W→ℕ)(b:Bool)(K L:Planet G I)(A:Site G I)(X: W→ Site G I)(U:Dance G I W): Prop where
   tour : WTour K L P x b A X R
   fields : Fields x μ K L A X U
variable (T: WChase P x (fun _=>planeF) R b K L A X U)(T': WChase P x (fun _=>planeF) R c K' L' B Y V)(M: Arch (Gulf P) K L A X R)(N: Arch (Gulf P) K' L' B Y R)(J: ArcS (Gulf P) K L K' L' A B X Y R)
include T T' M N J
lemma tissue_wide (S:Finset W)(n:ℕ)(hs:S.Nonempty)(hz:∀ v⊂ S,v.Nonempty→∀ k, Here false false Ϋ (U v k-V v k) (chips Ϋ*rateS Ϋ (charge R v)))(hf:∀ i<n,Bud P ( charge R S) eps_gain ( U S i-V S i ))(hp:2≤ S.card): Bud P (charge R S) eps_gain ( Src x (fun _=>planeF) K L A U S n - Src x (fun _=>planeF) K' L' B V S n ):= by
   let W0 i:= life P ( charge R S ) i eps_gain; intro k; unfold Src multi lonely; rw [ add_sub_add_comm,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]; apply Lease.plus
   · refine He_here (K:=Gulf P) _ (fun i hi=>?_) ( raised _ _ _ _ ); obtain he:i<n:= Finset.mem_Ico.mp hi |>.2; obtain hK : n-i>0:= by omega; -- change.S
     have hv:= hf i he k; rw [ show life P _ k eps_gain =_ from alter P ( charge R S ) k ] at hv ⊢; exact Trees M.main J.main ( N.states _ hK ) ( M.states _ hK ) ( J.states _ hK ) ( ( (moon_wide T'.tour T'.fields N hs i).2 hp k ).highp ) hv.highp ( raised _ _ _ _ ) cul
   · refine He_here ( K:=Gulf P ) _ (fun i hi=>?_) ( raised _ _ _ _ ); obtain ⟨H,hx,h,h'⟩:= n_small hi; rw [← Finset.sum_sub_distrib, ← toll_charge R H.le]; refine He_here (K:= Gulf P) _ ( fun j hj=>?_ ) ( raised _ _ _ _ ); --
     exact boats_wide (space_wide T.tour.plot hi) M.χ J.χ ( (moon_wide T.tour T.fields M hx j.1).1.highp ) ( ( moon_wide T'.tour T'.fields N hx j.1).1.highp ) ( (hz _ H hx j.1).highp ) ( ( moon_wide T'.tour T'.fields N h j.2).1.highp ) ( (hz _ h' h j.2).highp ) ( founded_wide T'.tour T'.fields hx _|>.2 ) (founded_wide T.tour T.fields hx _|>.2 ) ( founded_wide T.tour T.fields h _|>.2 ) ( founded_wide T'.tour T'.fields h _|>.2 ) T.tour.ground.pool T'.tour.ground.pool k
lemma tokens_wide (S:Finset W)(n:ℕ)(hs:S.Nonempty): Here false false Ϋ ( U S n-V S n ) (chips Ϋ*rateS Ϋ (charge R S)) ∧ ( S.card≥2→ Bud P (charge R S) eps_gain ( U S n-V S n ) ) := by
   induction S using Finset.strongInductionOn generalizing n with| _ S ih=>
      by_cases hu:2≤ S.card; swap; · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show S.card=1 from by obtain he:= Finset.card_pos.mpr hs; omega); refine ⟨?_,fun h=>False.elim ( hu h )⟩; rw [ T.fields.2.1, T'.fields.2.1, mul_comm, charge, Finset.sum_singleton ]; exact J.first i n
      induction n using Nat.strong_induction_on with| h n hx=>
        suffices he: Bud P (charge R S) eps_gain ( U S n-V S n ) from ⟨ marketing he,fun _=> he⟩; intro k; let r:=charge R S; let ℓ:= k+r+1; have hK : 0<( ℓ-r-eps_gain:ℝ):= by change 0< (( (k+r+1:ℕ):ℝ) - _ - 1/2 ); push_cast; linarith
        let X0:= Src x (fun _=>planeF) K L A U S n; let Y0:= Src x (fun _=>planeF) K' L' B V S n; let F:= sailP (fun _=>planeF) L; let G:= sailP (fun _=>planeF) L'; let Jw:=U S n; let H:=V S n; let D:= Jw-H; let W:=( F Jw-G H )+(X0-Y0); obtain hx':Here false false Ϋ (X0-Y0) ( life P r ℓ eps_gain ) := tissue_wide T T' M N J S n hs (fun i hi hp k=>( ih i hi k hp ).1) (fun j hj=>(hx j hj).2 hu ) hu ℓ; -- ih order?
        have hB: Fits false D W:= by unfold W; rw [← add_sub_add_comm]; exact Fits.subFit (motion_wide T.tour T.fields hs n) (motion_wide T'.tour T'.fields hs n); -- parser
        have hu' := emerged_wide T.tour T.fields hu n; have hv:= emerged_wide T'.tour T'.fields hu n;
        apply Lease.sticks (f:=plug D) _ (tilt (P:=P) ( m:=k) (n:=ℓ) (x:=eps_gain) ( h:=r ) (by unfold ℓ; omega)); refine marching (εGulf P) (raised _ _ _ _ ) hB.stroll ( Fits.positiveR hB ) ( Lease.minus (Midland hK.le b (hu'.1.pick ℓ)) (Midland hK.le c (hv.1.pick ℓ)) ) (aboveC Ϋ false ( combine hu'.2 hv.2 )) ?_; intro i hi hF E _ _ _ w hw ht; obtain ⟨ε,hε,hS⟩:= fertile (P:=P) hK E w ht (fun p=> Bool.noConfusion p); refine ⟨ _,_,hε, ?_,hS⟩;
        refine Lens.plus (F:=plug (F Jw-G H)) ?_ ( pinch hx' hi ) E w hw ht; rw [show life P r ℓ eps_gain= _ from alter P r ℓ] at *; exact LensD M.χ J.χ hF (pinch ( (moon_wide T'.tour T'.fields N hs n).2 hu ℓ ) (fun x=> Bool.noConfusion x)) hu'.1.mood hv.1.mood T.tour.ground.pool T'.tour.ground.pool cul ( raised P 0 r ℓ )
end YM.MS.Vane
