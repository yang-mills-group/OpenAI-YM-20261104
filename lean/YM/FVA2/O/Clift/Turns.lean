import YM.FVA2.O.Clift.Early
/-!
# Early-time inhomogeneous response estimate

`ahead`: using the past boundary condition, propagate the `Shy` size estimate
(power in ratio of scales, all powers), uniformly up through log scale θ
when we have that same cost on the forcing. See `Burst.keep`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Clift
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge}{B:Deck G} {K:Booked B}{M:MS_Data G K}{P:Geo I}
variable {F H:Glade G I}{q k n:ℕ}{b:ℤ}{X Y:T ( Glade G I )}
abbrev Shy (P:Geo I)(X: Glade G I): Prop:= ∀ q,totalT (deckB P) X (bare_age q) false
lemma age_step (hx:q≤k)(i:early P): bare_age k i ≤ bare_age q i:= exp_le_exp.mpr ( mul_le_mul_of_nonpos_right (Nat.cast_le.mpr hx) (sub_nonpos.mpr i.2.property ) )
lemma Step (h:∀ q:ℕ,0<q→ totalT (deckB P) F ( bare_age q ) false ): Shy P F:= fun i=> FormP.stays (h (i+1) (by omega)) ( age_step (Nat.le_succ i) )
lemma ahead (hr:∀ i:ℕ, Rake.collect ( X i ) )(hp:∀ i,Warm ( X i ) false)(hP:∀ i,Velocity (X i) ( Y i + helm M P.η X i ))(hv: ∀ i,PastPoint ( X i ))(hs:∀ i,Shy P ( Y i )) (n:ℕ): Shy P ( X n ):= by
    induction n using Nat.strong_induction_on with| h n IH=>
       apply Step; intro q hq; obtain ⟨k,h⟩:= hr n; have he(i:ℕ)(v:ℕ)(hv:k≤v+i): taxi (deckB P) (X n) ( bare_age q ) v:= by
           induction i generalizing v with
           | zero=>
              by_cases hv': k<v; · exact ( Well.unit (age_nn) ).takeM ( fun i w hz=> h i.1 i.2 w (by omega) );
              apply momentUp (hP n) (by exact ( show ∀ i,PastPoint ( X i ) from by assumption ) n) _ hq; apply ( Well.cram ( hs n q ) (fun i=>Bool.noConfusion i)).plus; apply helm_size early_live ( hp n ) _ (fun i hi=> (IH i hi q).part) age_nn; exact (Well.unit age_nn).takeM ( fun i w hz=> h i.1 i.2 w (by omega) )
           | succ i ih=>
              exact momentUp (hP n) (( ( show ∀ i,PastPoint ( X i ) from by assumption ) n )) ( Well.plus ( Well.cram ( hs n q ) (fun i=>Bool.noConfusion i) ) ( helm_size early_live ( hp n ) ( ih (v+2) (by omega) ) (fun i hi=> FormP.part ( IH i hi q )) age_nn )) hq
       exact form_of ( fun v _=> he k v (by omega) )
end YM.FVA2.O.Clift
