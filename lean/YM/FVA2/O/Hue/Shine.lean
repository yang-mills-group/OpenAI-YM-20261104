import YM.FVA2.O.Hue.Hill
/-!
# Realizing the free Taylor shifts with true continuum responses

Total includes using also exact terms; can thus insert any Ward-closed local
term here (`shine_seed`). Shifts constructed to keep all earlier orders
unchanged. See `Motion`, `Steps`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Hue
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Flux Book High Detect MS.Color MS.Local.Physical MS.Land Domain Convolve
open Lives O.Ward MS.City MS.Rake Outlook Tune O.Pad
open scoped Topology ContDiff
variable {I J :Type} {G:Gauge}{B:Deck G}{K: Booked B}{M:MS_Data G K}{P:IntervalFamily I}{η:I→ℝ}{n j d k h:ℕ}{b t:ℤ}{X Y:T ( Glade G I )}{a:I→ℝ}{f g:I→ Law G}{F:Law G}
lemma Profit.leaf (p:ℝ) : Profit P.dawn (fun (_:I)=>p):= ⟨‖p‖+1,(by positivity),0,( fun i=> by simp ) ⟩
structure Flame (M:MS_Data G K)(η:I→ℝ)(P:IntervalFamily I)(h n k:ℕ)(X:T ( Glade G I )) (F:I→ Law G) : Prop where
    uses : Total η M h P X
    low ( i : ℕ )( hp:i<n ): X i=0
    band: Diversity ( X n ) k
    top i s l (hp:l.length=k): X n i s l= F i l
namespace Flame
lemma plus (h1:Flame M η P h n k X f)(he:Flame M η P h n k Y g): Flame M η P h n k (X+Y) (f+g) := {
   uses:= Total.plus h1.uses he.uses
   low i hi:= by rw [Pi.add_apply,h1.low i hi,he.low i hi,add_zero]
   band:= uh h1.band he.band
   top i s l hp:= by simp only [ Pi.add_apply,h1.top i s l hp, he.top i s l hp ] }
lemma shade (h1:Flame M η P h n k X f)(hp: Profit P.dawn a): Flame M η P h n k (seat a X) (fun i=> a i • f i):= {
   uses:= h1.uses.starr hp
   low i hi:= by funext l; unfold seat pay; rw [ h1.low i hi,Pi.zero_apply,smul_zero ]
   band i t:= (h1.band i t).smul _
   top i s l hx:=by change (a i:ℂ) * X n i s l=_; rw [ h1.top i s l hx ]; rfl }
lemma zero : Flame M η P h n k 0 0:=⟨ Total.exists0,fun _ _=>rfl,fun _ _ _ _=>rfl,fun _ _ _ _=>rfl ⟩
lemma pile (s:Finset J){f:J→ I→ Law G}{X:J→ T ( Glade G I )}(hP:∀ i∈s,Flame M η P h n k (X i) (f i)): Flame M η P h n k (∑ i∈s,X i) (∑ i∈s,f i):= by classical induction s using Finset.induction_on with| empty=> rw [ Finset.sum_empty,Finset.sum_empty ]; exact zero| insert i s hi ih=> rw [ Finset.sum_insert hi, Finset.sum_insert hi ]; exact (hP i (by simp)).plus ( ih fun j hj=> hP j (mem_insert_of_mem hj) )
end Flame
abbrev Shine (M:MS_Data G K)(η:I→ℝ)(P:IntervalFamily I)(h n k:ℕ)(F:I→Law G): Prop:= ∃ X:T ( Glade G I ), Flame M η P h n k X F
lemma shine_pile (s:Finset J){f:J→ I→ Law G}(hF:∀ i,Shine M η P h n k (f i)): Shine M η P h n k (∑ i∈s,f i):= by
    choose Y hY using hF; exact ⟨_,Flame.pile s (fun i _=> hY i)⟩
lemma shine_cash (hp:Shine M η P h n k f)(hK:Profit P.dawn a): Shine M η P h n k (fun i=> a i • f i):= by obtain ⟨X,hX⟩:=hp; exact ⟨ _,hX.shade hK ⟩
lemma shine_extra (h:allowance P η){u:ℤ}(hp:F∈ Local.Physical.Lease G u j (-1)): Shine M η P k n j (fun _=> natQ F):= by
    rcases lt_or_ge u 0 with h'|h'; · rw [show F=0 from ?_,map_zero ]; exact ⟨0,Flame.zero⟩; ext w; exact ( lease_one.mp hp ).2.1.no_tall _ (fun i=>Bool.noConfusion i) (h'.trans_le ( show 0≤fieldDim wfield w from ( Int.natCast_nonneg _ ).trans ( length_pay w ) ))
    lift u to ℕ using h'; obtain ⟨X,hX,ht,hQ⟩:= O.Pad.generatorZ M hp h; exact ⟨ hold0 n ( nav M η X ), ( shift_R ( n:=n ) ).symm ▸ Total.q_form ( shift_Response hX ) ( shift_Q (Reps_desc ht (by omega)) ),(fun i hi=>low_hold hi),(by rw [hold_1]; exact hQ.reach),(by rw [hold_1]; exact hQ.tops )⟩
lemma single_i (q: Counter B h)(a:ℝ): Shine M η P h n (Land.read q.2).grade (fun _=> a • (Land.read q.2).read ):= by
    let X:= roadZ η M q; have hp:FlowZ (X 0) (Land.read q.2).grade ( Land.read q.2 ).read:= by obtain hp:= Mach.initialHF ( K.law _ q.2 ) ( Land.sizeG q.2 ) (M.markOK _ q.2); exact ⟨ fun i s=> hp.too (η i,s), fun i s l he=> ( Book.enough l (F:=X 0 i s) ( show (l.length:ℤ)= ( Land.read q.2).grade by rw [he] ) ).symm.trans (congr_fun ( hp.top (η i,s) ) l) ⟩ -- unif
    let Y:= seat (fun _:I=>a) X; refine ⟨ hold0 n Y, Total.unique_form q (Profit.leaf a), fun i hi=> low_hold hi,(by rw [hold_1]; exact fun i t=> (hp.reach i t).smul _), (by rw [hold_1]; intro i s l hx; unfold Y seat pay; simp only [Pi.smul_apply,hp.tops i s l hx]; rfl )⟩
lemma shine_seed (hp:F∈ Local.Physical.Lease G d k 0)(hc:natQ F=0)(hv:d≤h)(hT:allowance P η): Shine M η P h n k (fun _=> F) := by
    rcases lt_or_ge d k with h1|h1
    · rw [show F=0 from ?_]; exact ⟨ 0,Flame.zero ⟩; funext l; by_cases he:l.length=k; · refine (lease_one.mp hp).2.1.no_tall _ (fun i=>Bool.noConfusion i) ?_; have hz:= length_pay l; omega
      exact (lease_one.mp hp).2.2 l (fun i=>Bool.noConfusion i) he
    obtain ⟨p,K,hK,hE⟩:= B.combine hp hc
    have H(i: B.BIndex d k): Shine M η P h n k (fun _=> p i • B.raw d k i) := single_i ( q:= (⟨ ⟨d,Nat.lt_succ_of_le hv⟩,⟨ ⟨ k,Nat.lt_succ_of_le h1 ⟩,i ⟩⟩ : Counter B h) ) _
    obtain ⟨Y,hY⟩:=shine_pile Finset.univ H; obtain ⟨V,hV⟩:= shine_extra ( n:=n ) ( k:=h ) ( M:=M ) hT hK; rw [← hE]; refine ⟨ Y+V,?_⟩; convert hY.plus hV using 1; funext i; rw [Pi.add_apply, Finset.sum_apply]
end YM.FVA2.O.Hue
