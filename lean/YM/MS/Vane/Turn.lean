import YM.MS.Vane.Peel
/-!
# Differences at any Zone. Sheet operations.Saturation
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve City
open scoped Topology ContDiff Interval
variable { I E J:Type}{G:Gauge} {K L T Z:Planet G I}{b:Bool}{A B X Y:Glade G I}{P: Geo I}{h:ℕ}
variable {μ:I→Measure QP}{S:Belt I}{u v s q:S.time→ℝ}{r:ℕ}
lemma pea (B:Belt I): Mint B.price (fun _=>planeF) 5 := fun E _=> tom B.price 5 (by omega)
lemma beacon (B:Belt I): glob B.price (fun _=>planeF) 5:= Tall B.price 5 (by omega)
abbrev Flow (S:Belt I)(K:Planet G I)(u:S.time→ℝ):= Sheet S.price u (Job.plug K)
local notation "m0"=> (fun (_:I)=>planeF)
lemma LensC (hK: Flow S K 1)(hx:coinF false S A u (r+2))(hu:nn u): coinF false S ( sailP (fun _=>planeF) K A ) u r:= by
    obtain H:= penny hx hu hK (fun _=>zero_le_one) (beacon S) ( pea S ); rw [one_mul] at H; exact H
lemma LensD (hK: Flow S K 1)(he: Flow S ( K-L ) v)(hx: coinF false S ( A-B ) (v*u) (r+2)) (hy: coinF false S B u (r+2))( hA:Warm A false )( hB: Warm B false )( H:BackF K )( hL: BackF L )( hp:nn v )( hu:nn u ): coinF false S ( sailP (fun _=>planeF) K A - sailP (fun _=>planeF) L B ) (v*u) r := by
   obtain he': ∀ i t l,(sailP (fun _=>planeF) K A - sailP (fun _=>planeF) L B) i t l = ( sailP (fun _=>planeF) (K-L) B+sailP (fun _=>planeF) K ( A-B ) ) i t l := fun i t w=> willow (H:=B i t) (Sat_W hA H (fun _=>Coherent) i t) (fun x=> Bool.noConfusion x) ( Sat_W hB hL (fun _=>Coherent) i t) ( Sat_W hB H (fun _=>Coherent) i t);
   obtain hf:= LensC hK hx ( joy hp hu ); have heV:= penny hy hu he hp (beacon S) ( pea S ); apply reaches ( Lens.plus heV hf ) ; exact fun i v _ _=> he' i.1 i.2 v
-- Base diffusion along RHS.Source.Single orientation support with chip.
lemma thins (h:CourseK S.price v (plug K))(ht:Here true true S A (rateS S 4*u))(hx:Here false true S X s)(hp:nn u)(hu:nn v)(hU:nn s): Here false false S ( expJ K A X ) ( v*u*s ) := by
    have he:= trunks h ht hx hu ( joy (rateC _ _) hp ) hU; apply Lease.sticks he; intro i; unfold positive rateS; simp only [Pi.mul_apply]; rw [zpow_neg, show S.price.length i^(4:ℤ) = S.price.length i^(4:ℕ) from rfl]; apply le_of_eq; field_simp [( S.price.pos i|>.ne' )]
lemma Trees (hk: CourseK S.price 1 (plug K))(hL: CourseK S.price v ( plug ( K-L ) ))(hB:Here true true S B (rateS S 4))(hA:Here true true S A (rateS S 4))( ht: Here true true S ( A-B ) ( rateS S 4*v ) )(hy: Here false true S Y s)( hx:Here false true S (X-Y) (v*s))(hc:nn s)(hp: nn v): Here false false S (expJ K A X-expJ L B Y) (v*s):= by
   rw [show expJ K A X-expJ L B Y= expJ (K-L) B Y+expJ K (A-B) Y+expJ K A (X-Y) from funext fun i=> funext fun t=> twirlT ( A i t ) ..];
   have H0 : nn (1:S.time→ℝ):=fun _=>zero_le_one; refine Lease.plus ( Lease.plus ?_ ?_ ) ?_ -- cp partial
   · have hx:=thins hL (A:=B) (u:=1) (by simpa using hB) hy H0 hp hc; rw [ mul_one ] at hx; exact hx
   · have he:= thins hk ht hy hp H0 hc; rw [ one_mul ] at he; exact he
   exact shines S hk hA hx (joy hp hc)
-- join telescope given functional.Bill.C.Issue.`Describe abstract join premise
variable {z:I→QP}
lemma parkD (hA:Here false true S A u)(hB:Here false true S B u)(hV:Here false true S (A-B) (v*u))(ht:Here false true S Y s)(hY:Here false true S (X-Y) (v*s))(hos:Warm B false)(hom: Warm A false)(hy: Warm X false)(hZ: Warm Y false)(hL:BackF K)(hh: BackF L)(hT:∀ i,Cohere (μ i))
   (force1:∀ F H:Glade G I, Here false true S F u→ Here false true S H (v*s)→ Here false false S (regionC μ z K F H) q) ( force2:∀ F H:Glade G I, Here false true S F (v*u)→ Here false true S H s→Here false false S ( regionC μ z K F H ) q )(force3:∀ F H:Glade G I,Here false true S F u→Here false true S H s→Here false false S ( regionC μ z (K-L) F H ) q ): Here false false S (regionC μ z K A X - regionC μ z L B Y) q := by
    have heq : regionC μ z K A X-regionC μ z L B Y=regionC μ z K A ( X-Y )+regionC μ z K ( A-B ) Y+regionC μ z ( K-L ) B Y:= by funext i t; apply wirth ( room hy hom hL hT i t ) ( room hZ hom hL hT i t ) ( room hZ hos hL hT i t ) (room hZ hos hh hT i t);
    rw [heq]; exact Lease.plus ( Lease.plus (force1 _ _ hA hY) (force2 _ _ hV ht) ) (force3 _ _ hB ht)
where
    room {K: Planet G I}{F H: Glade G I}(hH: Warm H false)(hF: Warm F false)(hp: BackF K)(h:∀ i,Cohere (μ i))(i:I)(t:ℝ): SatP (μ i) (K i t) (F i t) ( H i t ) (z i) := by
       let T:=‖t‖+1; have ht: T≥0:= by unfold T; positivity
       let p:camp T:= ⟨(),t,existsC t⟩; obtain ⟨d,h,hV⟩:= Job.funds (camp T) (h i); exact priceP ( hp.cost i T ht ) ((hF.cost i T ht).highp) ((hH.cost i T ht).highp) hV p (z i)
end YM.MS.Vane
