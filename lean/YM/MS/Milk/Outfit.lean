import YM.MS.Milk.Fall
import YM.Next.RANK.GaussLeg
import YM.MS.Awning.Press
/-!
# Free Wilsonian solution ($MS physics$) in coordinate kernel.Design any actual alphabet
 and full cost constraints. Use signed Wick polynomial operations (Next.RANK.NORMAL).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Milk
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Analysis Submodule InnerProductSpace City Next.Rank Next.Rank.Normal Theater Drops Maxwell
open Tensor (diagonal)
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {A X:Type}{G:Gauge}{n d r:ℕ}{s:ℝ}{f:ℝ→ℂ}
local infix:70 " ⋆ "=> product (field Landau.parity)
local notation "Φκ"=> field (P:=QP) ( Landau.parity ( C:=G.ColorIndex ) ( A:=Axis ) )
variable {W E I:Type}{L:Album X G}{U V:ℝ→Law G}{g:X→Normal.poly X}
variable {u v:ℝ→ Normal.Symmetric X}{Q:Normal.Symmetric X}
-- root χ
open Labels Awning Logarithm
open Rake.Geo
open Alps Wire Outlook
variable {p q:Poly}{g Q':ℤ}
open Pearl Train Land Local.Physical Mach Menus
variable {B: Deck G}{M:Booked B}
abbrev gown (n) (t: Plaid B n)(x:ℝ)(A:MS_Data G M)(s:ℝ): Law G:= Outlook.four n ( A.marks n t 0 ) (x,s)
abbrev storm (n:ℕ)(u:Plaid B n): Pol G:= ΕData B (Land.read u)
lemma τmask (A:MS_Data G M)(t:Plaid B n): Wind.Leading.PhysicalHF ( Land.read t ) ( Archive n ( A.marks n t ) ):= initialHF ( M.law n t ) rfl ( A.markOK n t )
lemma marked_f (i:Glyph B n): Theater.orbit G ( ΕData B i )= i.read:= Theater.lamp_here B i.2.2
lemma chairman (t:ℝ)(i:Plaid B n)(A:MS_Data G M): ∀ s, gown n i t A s∈ Wallet G:= by
    intro s; let R:Geo Unit:= ⟨ fun _=>0,fun _=>t,fun _=>le_rfl⟩; obtain h := Rake.VeniceD R A ( Rake.Label.mk ( B:=B ) n i ) 0; exact Wallet.awake h.smooth () s
lemma father (i:Plaid B n)(x:ℝ)(A:MS_Data G M): Status (gown n i x A) ( fun s=> deep G s ( gown n i x A s )):= by
    let R:Geo Unit:= ⟨ fun _=>0,fun _=>x,fun _=>le_rfl⟩; have ht:= (τmask A i); refine ⟨ ⟨ _,fun v=> ht.too (x,v) ⟩,fun t w=>?_⟩; obtain H := Rake.VeniceD R A ( Rake.Label.mk ( B:=B ) n i ) 0 |>.motion () w t; rw [weightC ( chairman x i A t ) ]; simp only [lonely,Domain.paths,Finset.Ico_self,Finset.sum_empty,add_zero] at H; exact H
lemma hear0 (w:Legs ( Lane4 G )) (x:ℝ) (t:Plaid B n) (A:MS_Data G M) : Tendsto (fun s=> gown n t x A s w) atTop (𝓝 ( ( Theater.orbit G (storm _ t) ) w)):= by
    let i:= Land.read t; have h:=τmask A t; rw [ storm, marked_f ]; by_cases ht:w.length=i.grade
    · apply tendsto_const_nhds.congr fun s=>?_ ; obtain hp:= congr_fun ( h.top ( x,s ) ) w; rw [ enough w (by exact_mod_cast ht) ] at hp; exact hp.symm
    have he:w.length < i.grade ∨ i.grade< w.length:= by omega
    have hx := h.top ( x,x ); replace hv : i.read w=0:= (congr_fun hx w).symm.trans (strange _ ( show (w.length:ℤ)≠ (i.grade:ℤ) by omega)); rw [hv ]; obtain he|he:=he; · exact heart A t x w he
    exact tendsto_const_nhds.congr (fun s=> (h.too ( x,s ) _ (by exact_mod_cast he))|>.symm )
def Wrap (U:OM (Lane4 G)) : OM (Lane4 G):= fun s=> deep G s ( U s )
lemma Model {H:OM (Lane4 G)}(hU:Status U ( Wrap U+H ))(hV:Status V ( Wrap V + H ))(hx:∀ i,U i∈Wallet G)(ht:∀ i,V i ∈ Wallet G)(l:Filter ℝ)[l.NeBot](hp:∀ w,Tendsto (fun s=>U s w-V s w) l ( 𝓝 0 )): U=V:= by
   let Z:=U-V; have hz (t:ℝ): Z t∈ Wallet G:= ( Wallet G ).sub_mem ( hx t ) ( ht t ); have hu: Status Z (Wrap Z):= by
       obtain hv:= status_plus hU ( status_cast hV ( -1:ℂ ) ); simp_rw [ neg_one_smul, ← sub_eq_add_neg ] at hv; convert hv using 1; funext x; change deep G x ( U x - V x )= _+_-( _+_ ); rw [ map_sub ]; abel
   obtain ⟨n,hN⟩:= hu.life; refine sub_eq_zero.mp ?_; have he (k:ℕ) (x:ℝ) (w:Legs ( Lane4 G )) (h:w.length+k≥ n+1): Z x w=0:= by
       induction k generalizing x w with
       | zero=> exact hN x w (by omega)
       | succ k ih=>
          have hH (s:ℝ): HasDerivAt (fun t=>Z t w) 0 s:= by obtain hx:= hu.path s w; change HasDerivAt (fun t=> Z t w) ((deep G s) (Z s) w) s at hx; rw [weightC (hz s)] at hx; convert hx using 1; unfold Ccy; simp_rw [ at_trc, show ∀ i j:Lane4 G,Z s ( i::j::w )=0 from fun i j=> ih s _ (by simp; omega),mul_zero, Finset.sum_const_zero]; rw [integral_zero]
          exact tendsto_nhds_unique ( show Tendsto (fun j=> Z j w) l (𝓝 (Z x w)) from tendsto_const_nhds.congr (fun j=> is_const_of_deriv_eq_zero (fun t=>(hH t).differentiableAt) (fun t=>( hH t ).deriv) x j ) ) (hp w)
   exact funext fun x=> funext fun w=> he (n+1) x w ( by omega )
theorem opening (x:QP)(y:ℝ)(t:Plaid B n)(A:MS_Data G M)(s:ℝ): arc (storm n t) ( RawS G x ) (Bend G) s=chair G x (gown n t y A s):= by
    let X:= arc (storm n t) (RawS G 0) ( Bend G ); let Z:=gown n t y A; have he: X=Z:= by
       refine Model ( H:=0 ) (by rw [add_zero]; exact Milk.Lift (RealB ..) _) (by rw [add_zero]; exact father ..) (fun v=> ( show X v∈ Roof G from fills _ _ ).1) (chairman y t A) atTop (fun w=>?_ ); obtain h:= ( stableB (storm n t) 0 w ); rw [faith_m] at h; simpa only [sub_self] using! h.sub (hear0 w y t A)
    rw [ show gown n t y A s=X s from congr_fun he.symm _ ]; unfold X arc Tint; simp_rw [ LinearMap.comp_apply, readB,faith_m ];
end YM.MS.Milk
