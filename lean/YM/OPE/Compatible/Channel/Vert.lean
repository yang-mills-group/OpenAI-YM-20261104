import YM.OPE.Compatible.Channel.Wisps
/-! Density normalization by bouquet, no pinned topology issue. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset
open scoped Topology BigOperators Classical
variable {r n d m:ℕ}{T I:Type*} {u:ℝ}
namespace Script
open Page
variable (p:Script T r)
def bouquet (p:Script T r):Script T r:= ((Fintype.card (Equiv.Perm (Fin r)):ℝ)⁻¹) • ∑ a:Equiv.Perm (Fin r), swing a p
def stitch (p:Script T r):Script T r:= silt (bouquet p)
lemma adjusted {p:Script T r}(h:soot m p u): soot m (bouquet p) u:=by
   let n:ℝ:= Fintype.card (Equiv.Perm (Fin r)); have hn:0<n:=by unfold n; positivity; --
   apply ((Sack.finGather (B:=fun i:Equiv.Perm (Fin r)=>u) Finset.univ _ (fun i _=> swing_fee h i) (fun x=> zero_le_one.trans (payer m x))).scale_line n⁻¹).tips; simp only [sum_const,nsmul_eq_mul,card_univ,norm_inv,Real.norm_of_nonneg hn.le]; rw [← mul_assoc]; change n⁻¹*n*u≤ u; rw [inv_mul_cancel₀ hn.ne',one_mul]
lemma antics (a b:Equiv.Perm (Fin r)): swing a (swing b p) = swing (b.trans a) p:=rfl
lemma stir : sorted (bouquet p):=by
    intro q; ext v; change (((Fintype.card _):ℝ)⁻¹)*(∑ i:Equiv.Perm (Fin r),swing i p) (v ∘ q)=(((Fintype.card _):ℝ)⁻¹)*(∑ i:Equiv.Perm (Fin r),swing i p) v
    rw [Finset.sum_apply,Finset.sum_apply]; congr 1; exact Equiv.sum_comp (Equiv.mulLeft q) (fun i: Equiv.Perm (Fin r)=> swing i p v)
lemma stampV (h:Summable p): Idem (stitch p):=by
   have hs:Sack (figure 0) p (∑' i, ‖p i‖):= by unfold Sack figure poise; simp only [pow_zero,one_mul]; exact ⟨fun _=>norm_nonneg _,h.norm,le_rfl⟩
   have ht:= sootS (adjusted hs); refine ⟨rooted _,fun a=>by unfold stitch; rw [silt_symm a ht, stir p a]⟩
section
variable {N:Side}[Fintype T]
lemma reads_sum (t:Finset I)(p:I→Script T r) (h:∀ i∈t,Summable (p i))(x: Fin r→deck T N)(y:Site N): scribe y (∑ i∈t,p i) x=∑ i∈t,scribe y (p i) x:=by unfold scribe; simp_rw [Finset.sum_apply, Finset.sum_mul]; exact Summable.tsum_finsetSum fun i hi=> (instruments (p i) (h i hi) y x).summable
omit [Fintype T] in
lemma score_scaled (y:Site N)(p: Script T r)(x: Fin r→deck T N)(a:ℝ):scribe y (a • p) x=a*scribe y p x:=by unfold scribe; simp_rw [Pi.smul_apply,smul_eq_mul,mul_assoc,tsum_mul_left]
lemma scoring (h:Summable p)(y:Site N)(x:deck T N): value y (bouquet p) x=value y p x:=by
    let n:ℝ:= Fintype.card (Equiv.Perm (Fin r)); have hn: 0<n:=by unfold n; positivity
    unfold value bouquet; rw [score_scaled, reads_sum _ _ (fun i _=> swing_sum _ h i)]; change n⁻¹*(∑ i:Equiv.Perm (Fin r), value y (swing i p) x)=_; simp_rw [rotateValue, sum_const,nsmul_eq_mul]; rw [← mul_assoc]; change n⁻¹*n*value y p x=_; rw [inv_mul_cancel₀ hn.ne',one_mul]; rfl
lemma regaled (h:Summable p)(x:deck T N): narrate N (stitch p) x=narrate N p x:=by
    unfold narrate stitch; rw [← silt_read]; unfold library; apply sum_congr rfl fun i _=> scoring _ h i x
    apply sootS (m:=0); refine adjusted (u:=(∑' i,‖p i‖)) ?_ ; unfold soot Page.figure poise Sack; simp only [pow_zero,one_mul]; exact ⟨fun _=>norm_nonneg _,h.norm,le_rfl⟩
-- canon. if pin sym not Euler, but `stitch=silt bouquet=p`
omit [Fintype T] in
lemma pinnedBack (h:Summable p)(hb: Idem p): stitch p=p := by
   let n:ℝ:= Fintype.card (Equiv.Perm (Fin r)); have hn: 0<n:=by unfold n; positivity
   have hv(t:Finset (Equiv.Perm (Fin r))):silt (∑ i∈t,swing i p)=∑ i∈t,silt (swing i p):=by
       induction t using Finset.induction_on with
       | empty=> simp only [sum_empty]; unfold silt Sack.rope; ext; simp
       | insert i s hj ih=>
          have hz: Summable (∑ i∈s,swing i p):= by rw [show (∑ i∈s,swing i p)=(fun x=> ∑ i∈s,swing i p x) by ext; simp]; exact summable_sum (fun i _=>swing_sum p h i)
          rw [sum_insert hj,silt_add (swing_sum p h i) hz, ih,sum_insert hj]
   unfold stitch bouquet; rw [silt_scale,hv]; simp_rw [hb.2,sum_const]; ext j
   change n⁻¹*((univ.card:ℕ) • p) j=p j
   rw [Pi.smul_apply,nsmul_eq_mul]; change _* (n*p j)=_; rw [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul]
end
end Script
end YM.OPE.Flume
