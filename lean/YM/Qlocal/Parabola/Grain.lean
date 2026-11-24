import YM.Marker.Truncated
/-! Product estimate for full tracks, at arbitrary leased coefficient radii. Use not assuming κ multiplicative, permit supermultiplicative envelopes, pre-tail rescaling etc. Count no volume by retaining coefficient-specific bounds across arbitrarily many factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Parabola
open Marker Finset
open scoped Topology Classical BigOperators
variable {V : Type*} [DecidableEq V] {R: Census V}
abbrev Ray (R: Census V):= R.Mode→ℝ
variable {a b c:Poly R}{f g h w q: Ray R} {i: R.Mode}
open Marker.Poly
-- major term. size.Mat. f real positive.Twist.T.OrK.Body.En.
def realizer (f:Ray R) : Poly R:= Poly.inject (Complex.ofReal ∘ f)
def heightQ (f:Poly R):Ray R:= fun i=> (f.part i).re
def CoverP (f:Ray R)(x:Poly R):= ∀ i,‖x.part i‖ ≤ f i
lemma rayLeg (h:0 ≤ f)(i:R.Mode): ‖(realizer f).part i‖=f i:= by rw [show (realizer f).part i=(f i:ℂ) from rfl,Complex.norm_real]; exact Real.norm_of_nonneg (h i)
lemma meets (h:CoverP f a): 0≤ f:= fun i=> (norm_nonneg _).trans (h i)
lemma alto (h:0 ≤ f): CoverP f 0:= fun i=> by rw [Poly.part_nil,norm_zero]; exact h _
lemma fills0 (h:0 ≤ f): CoverP f (realizer f):= fun i=>(rayLeg h i).le
lemma merges_add (ha:CoverP f a) (hb:CoverP g b): CoverP (f+g) (a+b):= fun i=> by rw [Poly.part_plus]; exact (norm_add_le ..).trans (add_le_add (ha i) (hb i))

def click (f g: Ray R)(v:R.Mode):=∑ i,∑ j, if Poly.merges i j v then f i*g j else 0
lemma clickPos (h:0≤ f)(g':0≤ g):0 ≤ click f g:= fun i=> Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=> (by split; exact mul_nonneg (h _) (g' _); exact le_rfl)
lemma realizer_click : realizer (click f g)= realizer f * realizer g:= by
 ext1 i; rw [Poly.part_mul]; change (↑(∑ j,∑ k:R.Mode, if merges j k i then f j*g k else 0):ℂ)=_; simp_rw [Complex.ofReal_sum]; refine sum_congr rfl fun j _=> sum_congr rfl fun k _=> ?_; split_ifs; exact Complex.ofReal_mul ..; exact Complex.ofReal_zero
lemma realizer_inj : Function.Injective (realizer (R:=R)):= fun _ _ h=> funext fun i=>Complex.ofReal_injective (congr_arg (fun f:Poly R=> f.part i) h)
lemma performs (h1:CoverP f a)(h2:CoverP g b): CoverP (click f g) (a*b):=by
 intro i; rw [Poly.part_mul]; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun j _=> (norm_sum_le ..).trans (Finset.sum_le_sum fun k _=>?_); split_ifs; rw [norm_mul]; exact mul_le_mul (h1 j) (h2 k) (norm_nonneg _) (meets h1 j); rw [norm_zero]
variable {c d:ℝ}
structure Rental (w:Ray R) : Prop where
   pos (i:R.Mode):0 < w i
   multiply (i j k : R.Mode)(h:Poly.merges i j k): w k≤ w i*w j
   zero : w R.quiet=1
noncomputable def bill (u f:Ray R):ℝ:=∑ i,u i*f i
lemma bill_nn (hf:0≤ f)(hw:0≤w):0≤bill w f:= Finset.sum_nonneg fun i _=> mul_nonneg (hw _) (hf _)
lemma bill_add (u g h:Ray R): bill u (g+h)=bill u g+bill u h:= by simp only [bill,Pi.add_apply,mul_add,sum_add_distrib]
lemma bill_smul (t:ℝ)(u g:Ray R): bill u (t • g)=t*bill u g:= by unfold bill; rw [mul_sum]; apply sum_congr rfl; intro i _; exact mul_left_comm ..
lemma bill_scale_r (t:ℝ)(u g:Ray R): bill u (fun i=>g i*t)=bill u g*t:= by unfold bill; simp_rw [← mul_assoc, sum_mul]
namespace Rental
variable (p:Rental w)
include p
lemma oneSize:0≤ w:=fun z=> (p.pos _).le
lemma charge (hf:0≤ f)(hg:0≤ g): bill w (click f g) ≤ bill w f*bill w g:= by
 have hv(i j:R.Mode): (∑ k,w k* (if merges i j k then f i*g j else 0)) ≤ w i*f i*(w j*g j):= by
   by_cases h:∃ k,merges i j k; swap; · rw [Finset.sum_eq_zero (fun k _=>by rw [if_neg (show ¬merges i j k from fun hl=> h ⟨k,hl⟩), mul_zero])]; exact mul_nonneg (mul_nonneg (p.pos _).le (hf _)) (mul_nonneg (p.pos _).le (hg _))
   obtain ⟨k,hk⟩:=h; rw [sum_eq_single k]; rw [if_pos hk]; exact (mul_le_mul_of_nonneg_right (p.multiply i j k hk) (mul_nonneg (hf i) (hg j))).trans_eq (by ring)
   intro y hy hx; have ht:¬merges i j y:=fun he=> hx (Subtype.ext (he.2.symm.trans hk.2)); rw [if_neg ht,mul_zero]
   intro hk; exact (hk (mem_univ _)).elim
 unfold bill click; rw [sum_mul]; simp_rw [mul_sum]; rw [sum_comm]; refine sum_le_sum fun i _=>?_ ; rw [sum_comm]; exact Finset.sum_le_sum fun j _=>hv i j
end Rental
variable {α:Type*} (I:Finset α) (f: α→ Ray R)
def z0 (R:Census V): Ray R:= fun i=> if i= R.quiet then 1 else 0
lemma zO (R:Census V): realizer (z0 R)=1:=by ext i; rw [one_part]; change Complex.ofReal (if i=R.quiet then (1:ℝ) else 0)=_; split_ifs <;> simp
lemma unitC (p:Rental w): bill w (z0 R)=1:= by unfold bill z0; simp [p.zero]
noncomputable def grit := heightQ (∏ i∈I,realizer (f i))
variable {f} -- implicit α.R Binder
@[simp] lemma height_act (g:Ray R): heightQ (realizer g)=g:= rfl
lemma grit_read : realizer (grit I f) = ∏ i∈I,realizer (f i) := by
 induction I using Finset.induction_on with
 | empty => unfold grit; rw [prod_empty,← zO,height_act]
 | insert i s hi ih=> unfold grit; rw [prod_insert hi,← ih,← realizer_click,height_act]
-- f implicit in header? #check
variable (p:Rental q)
lemma grit_S (A:α→Poly R)(h:∀ i∈I,CoverP (f i) (A i)): CoverP (grit I f) (∏ i∈I,A i) := by
 induction I using Finset.induction_on with
 | empty => rw [grit,prod_empty,prod_empty, ← zO,height_act]; exact fills0 (fun i=> by change 0≤z0 R i; unfold z0; split <;>norm_num)
 | insert i v hi ih=> rw [prod_insert hi, show grit (insert i v) f=click (f i) (grit v f) from realizer_inj (by rw [grit_read,prod_insert hi,realizer_click,grit_read])]; exact performs (h i (mem_insert_self ..)) (ih fun i hi=>h _ (mem_insert_of_mem hi))
lemma grit_pos (h:∀ i∈I,0≤f i): 0≤ grit I f:= meets (grit_S I (fun i=> realizer (f i)) (fun i hi=> fills0 (h i hi)))
include p
lemma grit_fee (h:∀ i∈I,0≤ f i): bill q (grit I f)≤ ∏ i∈I,bill q (f i):= by
 induction I using Finset.induction_on with
 | empty => rw [grit,prod_empty,prod_empty,← zO,height_act,unitC p]
 | insert i v hi ih=>
   let H z (hz:z∈v):=h _ (mem_insert_of_mem hz); have h0:=h i (mem_insert_self ..)
   rw [prod_insert hi, show grit (insert i v) f= click (f i) (grit v f) from realizer_inj (by rw [grit_read,prod_insert hi,realizer_click,grit_read])]; exact (p.charge h0 (grit_pos _ H)).trans (mul_le_mul_of_nonneg_left (ih H) (bill_nn h0 p.oneSize))
end YM.Qlocal.Parabola
