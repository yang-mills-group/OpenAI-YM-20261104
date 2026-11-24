import YM.RGComparison.Core16.Stem.Accuracy
/-!
# Intermediate algebra for calculating the setup's Θ covariance, CP6
(power series notation, no analyticity in coupling obtained from these `point` comparison proofs).
-/
set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16.Silk
open Lumen Lattice RG Tree Wilson
open Function Filter Asymptotics
open PertExtension PertExtension.Series Tested
open scoped PowerSeries Topology BigOperators Classical

abbrev Roll:= PowerSeries ℝ
abbrev nth (r:ℕ)(x: Roll):= PowerSeries.coeff r x
def train (f:Cost)(x:Roll):Prop:= Aspiration f (term x)

-- Used to reconstruct finite stage receipts against planes, never choose formal coeffs from `train`.
variable {f g u: Cost}{x y: Roll}
lemma rail_bill {n:ℕ}(H: Bill n f)(e:f =ᶠ[Tested.germ] g): Bill n g:=by
  obtain ⟨c,hc,h⟩:=H; exact ⟨c,hc,(e.and h).mono (fun _ ⟨h₁,h₂⟩=>h₁ ▸ h₂)⟩
namespace train
lemma travel (H:train f x)(e:f =ᶠ[Tested.germ] g):train g x := fun n=> rail_bill (H n) (e.sub (Filter.EventuallyEq.refl _ _))
lemma unique (H:train f x)(W:train f y):x=y:=PowerSeries.ext fun _=>congr_fun (Aspiration.unique H W) _
lemma sand {v:ℕ→ℝ}(H:Aspiration f v):train f (PowerSeries.mk v):=by unfold train; rw [show term (PowerSeries.mk v)=v from funext fun i=>PowerSeries.coeff_mk ..]; exact H
lemma carries (H:train f x)(W:train g y): train (f+g) (x+y):=(by
    have h : Aspiration (f+g) (term x+term y):=Aspiration.add H W
    unfold train; rw [show term (x+y)= _ from (funext fun n=> show nth n (x+y)=(term x+term y) n from map_add ..)]; exact h)
lemma negate (H:train f x):train (-f) (-x):=by
   have h(n): peval (term (-x)) n= - peval (term x) n:= by
       funext t; simp [term,Zone.eval,peval,Finset.sum_neg_distrib]
   intro n; rw [h, neg_sub_neg, ← neg_sub]; exact bill_neg (H n)
lemma deduct (H:train f x)(W:train g y): train (f-g) (x-y):=by rw [sub_eq_add_neg,sub_eq_add_neg]; exact carries H W.negate
lemma produces (H:train f x)(W:train g y):train (f*g) (x*y):=by
   have hz(z:Roll):PowerSeries.mk (term z)=z:=by ext n; rw [PowerSeries.coeff_mk]; rfl
   simpa only [train, conv,hz] using (Aspiration.prod H W)
lemma mono (r:ℕ)(c:ℝ) : train (fun x=>x^r*c) (PowerSeries.monomial r c):=by
    have hf:=Aspiration.single c r; unfold train term; simpa only [PowerSeries.coeff_monomial, eq_comm, smul_eq_mul] using! hf
lemma cash (c:ℝ): train (fun _=>c) (PowerSeries.C c):= by
   simpa only [train,PowerSeries.monomial_zero_eq_C_apply,pow_zero,one_mul] using mono 0 c
lemma lift (H:train f x)(c:ℝ):train (c • f) (c • x):=by
   have h: PowerSeries.C c*x=c • x:=by ext n; simp
   rw [←h]; exact produces (cash c) H
lemma join {ι:Type*}(F:ι→Cost)(A:ι→ Roll)(t:Finset ι)(h:∀i∈t,train (F i) (A i)):train (∑ i∈t,F i) (∑ i∈t,A i):=by
   have hh:= Aspiration.sum t F (fun i=> term (A i)) h; unfold train; rw [show term (∑ i∈t,A i)=(∑ i∈t,term (A i)) from ?_]; exact hh
   funext; simp [term]
lemma compare (H:train f x)(W:train g y){n:ℕ}(he:Bill (n+1) (f-g))(i:ℕ)(hi:i ≤ n): nth i x=nth i y:= by
    have h:= Aspiration.vanish (deduct H W) he (show i<n+1 by omega)
    change nth i (x-y)=0 at h; exact sub_eq_zero.mp ((map_sub ..).symm.trans h)
-- θ chart coefficients through step proved to obtain finite budget from Asp.Allots
lemma money (H:train f x){V U:Lumen.Stage}{r:ℕ}{c:ℝ}(hc:V.Above U)(he:∀s,V.L ≤ s→ s^U.p*Forge.dollar s≤1)(ht:U.Ticket (r+2) c (f ∘ Forge.dollar)):
   Lumen.Fk.Allots V (term x) r (2*c) f:= by
    obtain ⟨_,hv⟩:= Lumen.Fk.buy hc he ht; exact hv.replace (Lumen.Fk.knows hv H)
end train
end YM.RGComparison.Core16.Silk
