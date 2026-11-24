import YM.QuadraticLocal.Normalization.Pulse
/-!
# Pre-reset model-β escrow: append M0 to an ordinary log output.

Carry the additional *unmarked* loans lifted as part of the formal step
(exact re-expression on flags). The error in `Canvas` (Resp. before reset)
does NOT pay the mask attachment costs. All on the same vacuum.

Widths / stature / positions independent of β after the step. Exposes
an explicit `Second` warrant conditioned on the price of this optional
merger; buying that margin before application is a separate step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary.Guard.Dusk
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n}
open Lapis Herb Weaving Morning
open Lattice RG Pressure Push.AbsoluteSums
open PhysicalNext Repeat

variable (h:Collection.Local X p v H w) (hG:G.Simple) (hB:R.Bounds c σ C Λ)(hc:Decent c p)(hW: Width p c σ)(hn:20 < n.val)(α:ℝ)
set_option quotPrecheck false
local notation "A"=> shelves X R p
local notation "D₁"=> Weaving.dawnK R c p X (nothing v) α 0
local notation "Y"=> softNeed G p c σ C α 0
local notation "u"=> Pipes.pours A D₁
local notation "v₁"=> (Pipes.fused (folio G n) p (Rack.widen A D₁))
-- basis price after school. New marker budget includes Flag merge.Supports.Unsorted
local notation "Z"=> Real.exp
open QuadraticLocal
open Audit
variable (M:Burn.Locale G) (x y β t:ℝ)
local notation "M₀"=> Devotion.basil (n:=n) p M
local notation "p★"=> (keys n)
local notation "𝔈"=> (Herb.deck (Burn.keys n) M₀ X)
local notation "𝔗"=> (Herb.ink (Burn.keys n) M₀ v)
-- `Capture`: keep log and E labels; mix Hard. This is easier than setting
-- every regular index via the final drawer dictionary, which we're under no
-- obligation to do on the pre-reset step. β now the predictive one.
def overwrite (r s:Activities G n): Activities G n:= ⟨r.reg,s.forced,r.E,s.K⟩
def shipment (P:PathData G)(c:Clip)(p:BudgetPoint)(X:Listing G n)(v:Collection.Source G n)(M:Burn.Locale G)(β α t:ℝ) : Rep G n:=
     { (Collection.frozen X P c p v (β+α) t) with activities:= overwrite ((Herb.deck (Burn.keys n) (Devotion.basil p M) X).read (Herb.ink (Burn.keys n) (Devotion.basil p M) v)) (Pipes.fused (folio G n) p ( Rack.widen (shelves X P p) ( Weaving.dawnK P c p X (nothing v) α 0 ))) }
variable (hv:∀ i:Site n, Till.Fairness p i (court i p.B) (M n i) x) (hτ: PhysicalNext.Repeat.Trio.Mirrors (M n))
variable (ξ :ℝ) -- y maybe duplicate?
variable (hP:Payments.Rates p.B ξ w (softNeed G p c σ C α 0) y)
local notation "Σ"=> shipment R c p X v M β α t
local notation "Q"=> ((Herb.deck (Burn.keys n) M₀ X).read 𝔗)
include hv hτ h
lemma receiptMark (U:Config G n): (Σ).activities.additive p U = Morning.news M p U+(X.read v).additive p U:=by
 let h₀ := Guard.basil_fit M hv hτ
 have he:= (Herb.showS (n:=n) (Burn.keys n) h h₀.1 U).1; change ((Q).additive p U)= _; rw [he]; apply congr_arg (fun z:ℝ=>z+(X.read v).additive p U) -- remove
 change (∑' i:Site n,_)=_; rw [tsum_fintype]; rfl

include hB hn hW hc hG
local notation "m:"=> (( fun U: Config G n => Z ((Collection.frozen X R c p v β t).exponent U - α*(Collection.receipt R c p U+ highH R p U)- Morning.news M p U) ))
lemma accounting (U:Config G n):
       m: U = Z ((Σ).exponent U)* Z (∑' i, (D₁).logarithm i U) := by
    have hx:= ex_cost h hG hB hc hW hn α β t U; change Z (_)=_; rw [← Real.exp_add, hx, (show (Σ).exponent U=t * (Fintype.card (Site n):ℝ)- R.inChannels c p (β+α) U -(Σ).activities.additive p U from rfl), receiptMark (R:=R) (c:=c) h α M x β t hv hτ ]; apply congr_arg; change (t*(Fintype.card (Site n):ℝ)- R.inChannels c p β U -(X.read v).additive p U)-_- _=_; ring
variable (hπ:Plateau.gardenfold p.B M)
structure Escrow (z:ℝ): Prop where
    -- κ captures. Split estimates in exactly same kernel. Require only regular Affordable before reset (no affine readout here). E_Reg total and remainder EBound separate: Paid through p+3. exponent tests independent.
    fullbudget : Collection.Local (Herb.deck (Burn.keys n) (Devotion.basil p M) X) p (Herb.ink (Burn.keys n) (Devotion.basil p M) v) (Guard.costM p x+H) w
    old : Collection.Local X p v H w
    splice : (Σ).activities.reg=(Q).reg ∧ (Σ).activities.E=(Q).E ∧ Nonempty (Burn.Seed (Σ) M) -- Prop? Seed Type
    attention : ((Σ).activities).ForcedFamily p ∧ (Σ).activities.KBound p ξ ∧ ∀ e d, Nonempty ((Σ).activities.Moves e d)
    photos : ∃ S:Kiosk.Second p (X.read v) (Σ).activities w ξ p.supportExponent z, (Audit.take G (Rack.widen S.skeleton S.tap) m:)= Real.exp ∘ (Σ).exponent
    depiction (U:Config G n) : (Σ).eval U = Guard.portal p α R c M X v β t U
include hπ hP
lemma affix (z:ℝ)(hZ:Payments.Rates p.B ξ w (Y+z) y): Escrow (R:=R) (c:=c) (p:=p) (X:=X) (v:=v) (w:=w) (H:=H) α M x β t ξ z:= by
 let V:=(Σ).activities; let H' := Guard.basil_fit M hv hτ; have he:= Herb.why (Burn.keys n) h H'.1; let S:=neutral_supply h hG hB hc hW hn α; have hw:= Ensemble.digest S hP; have hs: (v₁).Valid p 0 ξ:= hw.gates R c (β+α) t; have hL:= S.1; -- Fitting
 -- Kiosk receipts ownership
 refine ⟨he,h,⟨rfl,rfl,?_⟩,⟨?_,hs.boundK,fun l d=>?_⟩, ?_, fun U=>?_⟩
 · let u':= frozen X R c p v (β+α) t
   let E:= Burn.seed u' M hπ; exact ⟨E.model, E.reg, E.value,hπ⟩
 · let f:= hs.forced; exact ⟨f.sym,f.symtest,f.meas,f.meas_test,f.reads,f.reads_test,f.permit⟩
 · obtain ⟨t⟩:= he.transforms l d; obtain ⟨s⟩:= hs.moves l d; exact ⟨⟨t.ep,s.kp,t.reg_site,t.reg_support,s.forced_support,s.forced_inventory,s.forced_tests,t.valuesE,s.valuesK⟩⟩
 · obtain ⟨he,-,u',v',ht,hA,hL⟩:= S; refine ⟨⟨A,D₁,rfl,rfl,rfl,rfl,_,_,⟨he.steady,he.looks,he.reads,he.visits⟩,⟨v',hL.1,(fun i U=>(ht i U).2),hL.2⟩,hZ⟩,funext fun U=>?_⟩
   change m: U / Z (∑' i,(Rack.widen A D₁).logarithm i U)=_; rw [accounting h hG hB hc hW hn α M x β t hv hτ U, Rack.same_log, mul_div_cancel_right₀ _ (Real.exp_pos _).ne']; rfl
 · have ht' := hw.unshifted R c (β+α) t U; let F₁:=(trunk R c p A D₁ (β+α) t); let T:=(Σ); let MΓ : ℝ:= m: U; let L:= (∑' i,(D₁).logarithm i U)
   have hΨ: (finish R c p A D₁ (β+α) t).exponent U= F₁.exponent U:= by change t*_ - _- ((drawer G n).pours ( Rack.widen A D₁ )).additive p U= t * _-_ - (u).additive p U; rw [(Rack.preserves A D₁ p).same_sum]; rfl
   have hS:T.activities.gas p U=(X.read v).gas p U * Real.exp L:= by apply mul_left_cancel₀ (Real.exp_pos (F₁.exponent U)).ne'; unfold Rep.eval at ht'; rw [hΨ] at ht'; rw [←mul_assoc]; exact ht' 
   have hm:= accounting h hG hB hc hW hn α M x β t hv hτ U; unfold Guard.portal Rep.eval; change _*T.activities.gas p U=Real.exp _*(X.read v).gas p U * Real.exp _; rw [hS, mul_right_comm _ ((X.read v).gas p U) ( Real.exp _ ), ← Real.exp_add]
   rw [mul_comm ((X.read v).gas p U),← mul_assoc]; change ( Z ((Σ).exponent U) *Z (∑' i,(D₁).logarithm i U))*_ =_; rw [← hm]; apply congr_arg (fun z:ℝ=> z*((X.read v).gas p U)); apply congr_arg Real.exp; ring
end YM.AllOrder.Rosary.Guard.Dusk
