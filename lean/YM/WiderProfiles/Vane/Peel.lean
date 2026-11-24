import YM.MS.Vane.Peel
import YM.WiderProfiles.Vane.Rocket
import YM.WiderProfiles.Vane.Bee
/-!
WiderProfiles §F.1. Derivations extended from `YM/MS/Vane/Peel.lean`.
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
variable { I E J:Type}{G: Gauge}[ LinearOrder J ]{s:Finset J}{P:Geo I}{R: J→ℕ}{x:Position J I}
 {K L: Planet G I} {b:Bool} {X: Site G I}{A:J→Site G I}{Y: Dance G I J}{n k d:ℕ}{F H: Glade G I}{μ:I→Measure QP}
local notation "Ϋ"=> Gulf P
local notation "m0"=> (fun (_:I)=>planeF)
variable (h: WTour K L P x b X A R)(hx: Fields x (fun _=>planeF) K L X A Y)(hu:Arch ( Gulf P ) K L X A R)
include h hu
lemma germS_wide (_hp:2≤s.card)(n:ℕ)(hv:∀ t⊂ s,t.Nonempty→∀ i,Here false false Ϋ ( Y t i ) ( rateS Ϋ ( charge R t )))(hK:∀ i<n,Bud P (charge R s) 0 (Y s i)): Bud P (charge R s) 0 (Src x (fun _=>planeF) K L X Y s n):= by
    intro k; refine Lease.plus ?l ?r
    · exact He_here (K:=Gulf P) (Domain.paths n 0) (fun i hi=> ( shines Ϋ hu.main ( hu.states (n-i) (by obtain hp: i<n:= ( Finset.mem_Ico.mp hi ).2; omega)) (( hK i ( Finset.mem_Ico.mp hi|>.2 ) k ).highp) (raised P 0 (charge R s) k) )) ( raised _ _ _ _ ) -- unfold Src site.Actor ∑ & Λ
    · --  -- issue state after plus Lean metavars
      refine He_here (K:=Gulf P) _ (fun i hi=> He_here (K:=Gulf P) _ (fun k hk=> ?_) ( raised _ _ _ _ )) ( raised _ _ _ _ )
      obtain ⟨ Q,hg,H,hJ⟩:= n_small hi; rw [← toll_charge R Q.le]; exact lighting_wide hu.χ ( Rake.space_wide h.plot hi ) ((hv i Q hg k.1).highp) (( hv _ hJ H k.2 ).highp) _
include hx
lemma moon_wide (hs:s.Nonempty)(n:ℕ): Here false false Ϋ ( Y s n ) ( rateS Ϋ (charge R s) ) ∧ ( s.card≥2→ Bud P (charge R s) 0 ( Y s n )) := by
    induction s using Finset.strongInductionOn generalizing n with| _ s ih=>
       by_cases hp:s.card≥2; swap; · obtain ⟨k,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from by obtain hx:= Finset.card_pos.mpr hs; omega); refine ⟨?_,fun h=>False.elim (hp h)⟩; rw [hx.2.1]; simpa only [charge,Finset.sum_singleton] using hu.first k n -- `first` gives ∀ t≥ all.
       induction n using Nat.strong_induction_on with | h n hM=>
          suffices he: Bud P (charge R s) 0 ( Y s n ) from ⟨ more he,fun _=> he⟩; intro k; let F:= Y s n; let H:= Src x (fun _=>planeF) K L X Y s n; let Q:=charge R s; let N:=k+Q+1; let V:=Gulf P; let p:= life P Q N 0; have he:= Fits.positiveR (P:=P) (motion_wide h hx hs n); have hU:= emerged_wide h hx hp n; have hi : 0<( N-Q-(0:ℝ) ):= by unfold N; push_cast; linarith
          have hc:Bud P Q 0 H:= germS_wide h hu hp n (fun t ht hs n=> (ih t ht hs n).1) (fun i hi=> (hM i hi).2 hp );
          apply Lease.sticks (S:=V.price) (f:=plug F) _ (tilt (P:=P) ( x:=0 ) ( h:=Q ) (show k≤ N from by unfold N; omega)); refine marching (εGulf P) ( raised _ _ _ _ ) ( winter_wide h hx hs n|>.walk ) he ( Midland hi.le b ( hU.1.pick N )) ( aboveC V false hU.2 ) ?_
          intro r hr hF E _ _ _ w hw ht; obtain ⟨ε,hε,hS⟩:= fertile (P:=P) hi E w ht (fun h=> Bool.noConfusion h); have hW := penny hF ( raised _ _ _ _) hu.χ ( fun i=> zero_le_one ) (Tall V.price 5 (by omega)) (fun E _=> tom V.price 5 (by omega) ); rw [one_mul] at hW; exact ⟨_,_,hε, Lens.plus hW ( pinch ( hc N ) hr ) E w hw ht, hS⟩
end YM.MS.Vane
