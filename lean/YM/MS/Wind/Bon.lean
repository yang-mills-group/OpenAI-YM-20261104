import YM.MS.City.Moves
/-!
# Packing finite-memory positions

Wind data use full sym/color on off-net kernels, all t,y. Rotation needed for
 bulk = net. No master equation assumed. Preserve under solve.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}
abbrev Flow (G:Gauge):= BF (BH G) QP
abbrev Pack (G:Gauge):= ℝ→ Flow G
abbrev Dec (G:Gauge):= T (Pack G) -- avoid symbol
variable {F H:Flow G}{P Q:Pack G}{b:Bool}{u v:ℤ}{r:ℕ} {I:Type}
-- Smooth width and rank capacity
structure Bon (b:Bool)(q:ℤ)(F:Flow G): Prop where
   joint: TouchF F
   sym (t:ℝ): Symm (field parity) (F t)
   perk (t:ℝ): Perk (F t)
   real (t:ℝ): World (F t)
   pulse (t:ℝ): wins (F t) q
   t_color (t:ℝ)(i:G.El): repeatC i (F t)=F t
   stand (t:ℝ): b=true → SignedScope true (F t)

def Rank (F:Flow G)(q:ℤ): Prop:= ∀ t, Limit (F t) q
structure Fees (b:Bool)(q:ℤ)(P:Pack G): Prop where
   stay x: Bon b q (P x)
   pay: ∃ r:ℕ,∀ x, Rank (P x) r
   currency: Ready P

-- operations
namespace Bon
variable (h:Bon b u F)
include h
lemma sum2 (he:Bon b u H): Bon b u (F+H) where
   joint:= h.joint.add he.joint
   sym t:= (h.sym t).add (he.sym t)
   perk t:= (h.perk t).add (he.perk t)
   real t:= fun w=> by simp only [Pi.add_apply,h.real t w, he.real t w, star_add]
   pulse t:= Rails.add (h.pulse t) (he.pulse t)
   t_color t i:= by simp only [Pi.add_apply,map_add,h.t_color t i,he.t_color t i]
   stand t h':= (h.stand t h').add (he.stand t h')
lemma smul (c:ℂ)(he:star c=c): Bon b u (c • F) where
   joint:= h.joint.scale c
   sym t:=(h.sym t).smul _
   perk t:=(h.perk t).spin _
   real t:= fun w=> by simp only [Pi.smul_apply,smul_eq_mul,star_mul',h.real t w,he]
   pulse t:= Rails.smul _ (h.pulse t)
   t_color t i:= by rw [Pi.smul_apply,map_smul,h.t_color]
   stand t h':=(h.stand t h').scalar c
lemma car (t:ℝ): Solid b (F t) u := ⟨fun l i j r _=> h.sym t l i j r, fun w _ hv=> h.pulse t w (chargeF w |>.symm ▸ hv), fun w _ i=> by rw [← rep_book,h.t_color],fun w _=> h.real t w⟩
lemma turnt (t:ℝ): Pure (field parity) (Local.parity u) (F t):= Rails.parity (v:=ghostNo ∘ Prod.fst) (fun i=> Native.ghostParity i.1) (h.pulse t)
omit h in
lemma zeroes : Bon b u (0:Flow G):= ⟨TouchF.zeros,fun _=> Symm.zero, fun _=> Perk.zeros,fun _ _=> (star_zero _).symm,fun _=> Rails.zero, fun _ _=> map_zero _,fun _ _ _ _ _=> mul_zero _⟩
omit h in
lemma allsum (s:Finset I){F:I→ Flow G}(H:∀ i∈s,Bon b u (F i)): Bon b u (∑ i∈s,F i):= by
    classical
    induction s using Finset.induction_on with| empty=> simpa using zeroes (G:=G) (b:=b) (u:=u)| insert i s hi ih=> rw [Finset.sum_insert hi]; exact (H i (by simp)).sum2 (ih (fun i hi=> H i (mem_insert_of_mem hi)))
end Bon
namespace Rank
variable (h:Rank F u)
include h
lemma add (he:Rank H u): Rank (F+H) u:=fun t=> Limit.add (h t) (he t)
lemma sub (he:Rank H u): Rank (F-H) u:=fun t=> Limit.sub (h t) (he t)
lemma pay (hv:u≤v): Rank F v:= fun t=>(h t).up hv
lemma smul (c:ℂ): Rank (c • F) u:= fun t=>(h t).smul c
omit h in
lemma zero (G:Gauge) (u:ℤ): Rank (0:Flow G) u := fun _ _ _=> rfl
omit h in
lemma taps (s:Finset I){F:I→Flow G}(h:∀ i∈s,Rank (F i) u): Rank (∑ i∈s,F i) u:= by intro t; simp_rw [Finset.sum_apply]; exact Limit.sum _ fun i hi=> h i hi t
lemma gone (he:u<0) : F=0:= by funext i; ext l; exact h i l (by omega)
end Rank
namespace Fees
variable (h:Fees b u P)
include h
lemma sum2 (hh:Fees b u Q): Fees b u (P+Q) where
   stay x:=(h.stay x).sum2 (hh.stay x)
   currency:= h.currency.add hh.currency
   pay:=by obtain ⟨r,H⟩:=h.pay; obtain ⟨t,h⟩:=hh.pay; exact ⟨r+t,fun x=> Rank.add ((H x).pay (by omega)) ((h x).pay (by omega))⟩
lemma fare (v:ℝ): Fees b u (v • P) where
    stay x:= by change Bon b u ((v:ℂ) • P x); exact (h.stay x).smul _ (by simp)
    currency:= h.currency.scale v
    pay:= by obtain ⟨r,H⟩:=h.pay; exact ⟨r,fun x=> by change Rank ((v:ℂ) • P x) r; exact (H x).smul _⟩
omit h in
lemma zero (u:ℤ)(G:Gauge): Fees b u (0:Pack G):= ⟨fun _=> Bon.zeroes, ⟨0,fun _=> Rank.zero G 0⟩, Ready.zero⟩
omit h in
lemma sum (s:Finset I){F:I→Pack G}(h:∀ i∈s,Fees b u (F i)): Fees b u (∑ i∈s,F i):= by
    classical
    induction s using Finset.induction_on with| empty=> simpa using zero (b:=b) u G| insert i s Hi ih=> rw [Finset.sum_insert Hi]; exact (h i (by simp)).sum2 (ih (fun i hi=> h i (mem_insert_of_mem hi)))
end Fees

-- actual seed Circle
private def bornLm (G:Gauge): Dot G Cover →ₗ[ℝ] Flow G:= LinearMap.pi (fun _=> run.restrictScalars ℝ)
def borne (f: Dot G Cover) : Flow G:= fun _=> run f
lemma openOrigin (F:Actor G)(k:ℕ)(h:Circle G F b u): Fees b u (fun x=> borne (F x k)) where
    stay x:= {
       joint:= run_this _ _
       sym t:= tied.sym (F x k) (h.actual k x).symm
       perk _:= Perk.perk_origin _ (h.actual k x).symm
       pulse _:= fun w H=> (blockSolid u (F x k) (h.actual k x) (h.settled k x) false).ghost w (fun v=> Bool.noConfusion v) (chargeF w|>.symm ▸ H) -- orientation
       t_color _ p:= by change repeatC p (run _)= _; rw [caps,h.settled]; rfl
       real _:= fun w=> (mirror_bill (F x k) (h.actual k x).still w).symm
       stand _ e:= choral _ (h.stance0 _ _ e) }
    pay:= by obtain ⟨v,hv⟩:=h.room k; exact ⟨v,fun x _=> Tone.oneRank (hv x)⟩
    currency:= Ready.linear (h.tag k) (bornLm G)
-- productivity etc
end YM.MS.Wind
