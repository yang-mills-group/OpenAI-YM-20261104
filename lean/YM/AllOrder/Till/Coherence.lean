import YM.AllOrder.Till.Neutral
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Till
open Lattice Laurent RG Gauge Filter Tree Metric Finset Bloch
open Push.Uniform Precision Bid Wilson Push Exterior Pressure Function Matrix
open Extra.Iteration Push.AbsoluteSums Plateau
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {k w:ℕ} {n : Side}
local notation "T" => RG.Atom G k
open AnalyticBridge VerifiedReset Next.Scheduling
open Floe StateE
variable {p:BudgetPoint}{u:Site n} {X:Support n}{C B:ℝ}
-- abstraction for regular rendering errors; supports covariance holds outside this
structure Fairness (p:BudgetPoint)(u:Site n)(X:Support n)(f:Config G n→ℝ)(C:ℝ):Prop where
 ready : p.Regular X f
 cap : p.supBounds u X f C
 one : f 1=0
 he : Nonwrapping X u→ ∀ v:LinearJet G, logHessian f (v.field u) (v.field u)=0
namespace Fairness
variable {f g:Config G n→ℝ}{h:C=B→ Prop} -- test
lemma nth (h:Fairness p u X f C)(he:Nonwrapping X u) : ∀ v z,IsAffineDirection u v→ IsAffineDirection u z→logHessian f v z=0:= affine_zero h.ready u (h.he he)
lemma scale (h:Fairness p u X f C)(x:ℝ): Fairness p u X (x • f) (|x| *C):= by
 refine ⟨CouplingShape.reg_scale _ h.ready,CouplingShape.sup_scale _ h.cap,by simp [h.one],fun he i=>?_⟩; let a:=i.field u; have hh:ContDiffAt ℝ 2 (f ∘ increment 1) 0:= germ_diff h.ready; unfold logHessian;
 -- scalar
 change iteratedFDeriv ℝ 2 (x • (f ∘ increment 1)) _ _= _; rw [iteratedFDeriv_const_smul_apply (a:=x) hh]; change x*logHessian f a a =_; rw [h.he he i,mul_zero]
lemma enroll {ι:Type}{f:ι → Config G n→ℝ}{v:ι→ℝ}(s:Finset ι) (h:∀ i∈s,Fairness p u X (f i) (v i)): Fairness p u X (∑ i∈s,f i) (∑ i∈s,v i):= by
 obtain ⟨hx,hv⟩:=good_sum p s (fun i hi=> ⟨(h i hi).ready,(h i hi).cap⟩); have he := (funext (fun x=> (Finset.sum_apply x s f)))
 refine ⟨he ▸ hx, he ▸ hv, ?_,fun ht i => ?_⟩
 · rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun i hi=> (h i hi).one
 let a:= increment (1:Config G n); have hu:(∑ i∈s,f i) ∘ a=∑ i∈s,(f i) ∘ a:= funext fun v=>by simp only [Function.comp_apply,Finset.sum_apply] -- simp
 change iteratedFDeriv ℝ 2 ((∑ i∈s,f i) ∘ a) 0 _=0; rw [hu,iteratedFDeriv_sum_apply (fun i hi=>germ_diff (h i hi).ready), _root_.sum_apply]; exact Finset.sum_eq_zero fun j hj=>(h j hj).he ht i
lemma le (h:Fairness p u X f C)(hq:C≤B):Fairness p u X f B:= {h with cap:=sup_le h.cap hq}
lemma transport (x:Seat n) (h:Fairness p 0 X f C)(hc:4≤ n.val) (g:G.Simple): Fairness p x.2 (x.spread X) (f∘ x.view) (Push.Local.turnCost p.order p.power*C):= by
 refine ⟨x.regular h.ready,x.sup h.ready h.cap,?_,fun v i=>(x.hessian g h.ready v hc i i).trans (h.he (x.unwrapped v) _)⟩;
 unfold Function.comp Seat.view; rw [pull_one_field]; exact h.one
lemma wider (h:Fairness p u X f C) {Y}(he:X⊆Y):Fairness p u Y f C:= ⟨reg_larger h.ready he, sup_larger h.cap he, h.one,fun ht=> h.he (fun i hh=> ht i (he hh))⟩
end Fairness
namespace Tilt
variable (s:ℕ→Atom G k) (p:BudgetPoint)(U:Config G n)(o:Site n)(w:ℕ) {t C:ℝ} (h:Quoted s t C)(ht:0<t)(hw:4*k≤w)
def print (n:Side)(x:Site n) := anchorV (legible s w) w n x
local notation "f"=>legible s w
lemma crop_self(w:ℕ)(hk:4*k≤ w) : Plateau.cutA (legible s w) w=legible s w:= funext fun i=> if_pos (window_cost _ _ hk)
lemma print_out : gardenfold w (print s w):= anchor_local (legible s w) w
lemma signs(n:Side): PhysicalNext.Repeat.Trio.Mirrors (print s w n):= anchor_turn (legible s w) w n
include hw
open PhysicalNext Repeat
lemma reads: ∑ x:Site n, print s w n x U=Extra.Iteration.action (legible s w) U:= by unfold print; rw [anchor_whole, crop_self s w hw]; rfl -- simp wrong unfolding lhs
omit hw
variable (z:Seat n)
lemma projected : z.spread (court 0 w) = court z.2 w:= by
 let s:=Push.Local.turnSites z.1 z.2; change Finset.image (s) _=_; rw [← Push.Local.halo_map s (Push.Local.turn_sep _ _),Finset.image_singleton,show s 0=z.2 from Seat.turn_zero _] -- change throw

include h ht hw
local notation "Z"=>nextV.soul s w (0:Site n)
lemma price_tag : print s w n o=(Fintype.card Signed:ℝ)⁻¹ • (∑ v:Signed, (Z) ∘ Seat.view (v,o)):= by
 ext1 U; unfold print Plateau.anchorV; rw [crop_self s w hw]; unfold Patch.average; rw [Pi.smul_apply, Finset.sum_apply]; change _= ((_:ℝ)⁻¹)* _; apply congr_arg; refine Finset.sum_congr rfl fun v _=>?_; simp only [Function.comp_apply,Seat.view]; rw [nextV.plies s _ _ w h ht hw]; apply tsum_congr; intro j; unfold Atom.unmasked RG.Slot.atSite; simp_rw [expandAt_pull,affine, Signed.act_zero,zero_add]; rfl -- aTerm maybe
local notation "A"=>print s w n o
abbrev bill (G:Gauge)(p:BudgetPoint)(w k:ℕ)(C:ℝ):ℝ:= Push.Local.turnCost p.order p.power*(C*(Wages.startup G k p.power p.order *p.threshold^k*(1+(w:ℝ))^(Wages.grade k p.power p.order)))
lemma fair (hk:2 ≤ k)(hn:4≤n.val)(g:G.Simple): Fairness p o (court o w) (A) (bill G p w k C):= by
 have he:Fairness p 0 (court (0:Site n) w) Z (C*(Wages.startup G k p.power p.order*p.threshold^k*(1+(w:ℝ))^Wages.grade k p.power p.order)):= ⟨(nextV.esprit s p 0 w h ht hw).1,(nextV.esprit s p 0 w h ht hw).2,nextV.one s 0 w (by omega),fun he i=>nextV.neutral s p 0 w h ht hw hk he hn g i⟩
 rw [price_tag s o w h ht hw]; refine (Fairness.scale (Fairness.enroll univ (fun (i:Signed) _=> (?_ : Fairness p o (court o w) (Z ∘ Seat.view (i,o)) (bill G p w k C)))) ((Fintype.card Signed:ℝ)⁻¹)).le ?_
 · let Z':Seat n:=(i,o); exact projected w Z' ▸ he.transport Z' hn g -- cast maybe.S.c
 have hh:0<(Fintype.card Signed:ℝ):=by exact_mod_cast Fintype.card_pos
 have hV:0<(Fintype.card Signed:ℝ)⁻¹:=inv_pos.mpr hh; simp only [sum_const,card_univ,nsmul_eq_mul,abs_of_pos hV,inv_mul_cancel_left₀ hh.ne']; exact le_rfl
end Tilt
end YM.AllOrder.Till
