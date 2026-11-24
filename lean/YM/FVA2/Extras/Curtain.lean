import YM.FVA2.Extras.Entrance
/-! # Preparing to evaluate the reduction on a full `Scriven` setup

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
variable {W:Type} {X Y:T (localX G)}{x:Unit→QP}{a:ℝ}
local notation "Q₀"=> Tide.frameF Unit a
lemma KnownAt (H:Honest a X b)(i:ℕ): Known Q₀ ( X i ):= by
    let P:= Tide.frameF Unit a; refine ⟨-b,fun E _ _ w he hh=>?_⟩; obtain hK:= (H i) E w he hh; let V:= Lower P; refine ⟨ fun i=> hK.smooth ( tstart i ),fun k=>?_⟩; obtain ⟨C,hC,m,hk⟩:= hK.quoted k; refine ⟨ C,hC,m,fun i p ht=> le_trans (hk (tstart i) p trivial) ?_⟩; change C*((FullEra a).toScale).full.cheap ( tstart i ) p^m* ( exp (tstart i) ^ pitch w *_*_ ) ≤ C*(V.full.cheap i p)^m*( V.length i ^ pitch w*_*_ ); have hV: V.length i=exp ( tstart i ):= coldE P _; simp only [Cool.stamp, (by exact hV : V.length i=_),show (FullEra a).length (tstart i)=V.length i from hV.symm ]; have hx : ( FullEra a ).toScale.full.cheap (tstart i) p ≤ V.full.cheap i p:= by
       unfold Scale.full Scale.weight; change (1+‖a‖+‖tstart i‖)*(1+exp (tstart i)*‖p‖ ) ≤ (1+|a|)*(1+|tstart i|)*(1+V.length i*‖p‖); rw [hV,Real.norm_eq_abs,Real.norm_eq_abs]; gcongr; nlinarith [abs_nonneg a,abs_nonneg (tstart i)]
    apply mul_le_mul ?_ (le_of_eq ?_) ?_ ?_
    · have hz:= (( FullEra a ).toScale).full.cheap_pos (p:=p) (i:=tstart i) trivial; gcongr
    · change exp _ ^_* exp _ ^(-b)*exp _ ^k=exp _^ _*V.length i ^(-b)*exp _^k; rw [hV]; rfl
    · positivity
    have hh:= V.full.cheap_pos (p:=p) (i:=i) ht; positivity
lemma Estate (hp: Honest a X b)(ht:Response X M (logMass a) d)(hx:Unit→QP): Field Q₀ M (hx,X) d:= ⟨ht,⟨‖hx ()‖+1,by positivity,fun i=> le_add_of_nonneg_right zero_le_one⟩, KnownAt hp ⟩
-- all positions change independent. central-probe.
variable {L:List (Cart G Unit)}{h:ℕ}{p:T (Package B h)}{Z:T (localX G)}{U: Land.Plaid B h→ T (localX G)}
-- actual arrays comparison pointwise + all orders
abbrev Udef (U:Land.Plaid B h→ T (localX G))(p:T (Package B h)):= ∑ i:Land.Plaid B h, Source (U i) (fun j=>p j i)
lemma paradeC {S:T (localX G)}(hS: Lucent Q₀ M 0 S ( nest L x ( nav M (logMass a) Y ) ))(he:X=many a M p+nav M (logMass a) Y)(hV:∀ i, Lucent Q₀ M 0 ( U i ) ( nest L x ( soloV h (logMass a) M i ) )): Lucent Q₀ M 0 ( Udef U p + S ) (nest L x X):= by
    rw [he,map_add,many,map_sum ]; refine added ?_ hS; apply summing _; intro i hi; change Lucent _ _ _ _ (nest _ _ (Source (soloV _ _ M i) _)) ; rw [ circleN ]; exact freed (hV i) _
lemma money_alm (p:T (Package B h))(hV:∀ i, Lucent Q₀ M 0 ( U i ) ( nest L x ( soloV h (logMass a) M i ) )) : assessment (Udef U p) () n= ∑ i:Land.Plaid B h, ∑ j∈ Finset.range (n+1), (p j i:ℂ)* assessment ( U i ) () (n-j) := by
    let Y' (i:Land.Plaid B h):= Source (U i) (fun j=> p j i)
    have HH(i): Response ( Y' i ) M ( Tide.frameF Unit a ).η 0:= ( freed ( hV i ) ( fun j=> p j i ) ).1
    unfold Udef; change assessment ( ∑ i, Y' i ) () n=_; rw [ grants_all (P:=Tide.frameF Unit a) () Finset.univ ( X:=Y' ) ( fun i _=> HH i ),Finset.sum_apply ]; exact Finset.sum_congr rfl fun i _=> grants () (hV i) _
lemma upland (he:X=many a M p+nav M (logMass a) Y)(hm:Lucent Q₀ M 0 Z ( nest L x X ))(hp:ghostly a M Y ((h:ℤ)-1) )(ht:Scriven Q₀ M (x,X) L 0)(hV:∀ i, Lucent Q₀ M 0 ( U i ) ( nest L x ( soloV h (logMass a) M i ) ))(hD:publicW Q₀ M L) : assessment Z () n= ∑ i:Land.Plaid B h, ∑ j∈ Finset.range (n+1), (p j i:ℂ)* assessment ( U i ) () (n-j) := by
    have hx : Scriven Q₀ M (x,Y) L (-1):= ⟨ Estate hp.2 hp.1 x,ht.others,ht.apart,ht.among ⟩
    obtain ⟨V,h'⟩:= script rfl hx
    let S:= nav M (logMass a) V
    obtain hS : Lucent Q₀ M 0 S ( nest L x ( nav M (logMass a) Y ) ):= by
        let Y': Cart G Unit:= (x,Y)
        -- transport defeq without cost
        have hL:= herein (b:=-1) rfl hx hD h'
        rw [show (-1:ℤ)+1=0 from (by omega)] at hL
        exact hL
    have hv : Lucent Q₀ M 0 ( Udef U p+ S ) (nest L x X) := paradeC hS he hV
    have he' : Response (Udef U p ) M (logMass a) 0:= Response.all_fin _ (fun i _=> ( freed ( hV i ) ( fun j=> p j i ) ).1 )
    rw [ unique_resp hm hv, grants_plus (P:=Tide.frameF Unit a) () he' hS.1, Pi.add_apply, show assessment S () n=0 from closeQ h'.1 () n,add_zero ]; exact money_alm p hV
end YM.FVA2.Extras
