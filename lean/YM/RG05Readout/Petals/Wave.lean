import YM.RG05Readout.Petals.Nib
/-!
# Literal lattice SBP stencil on ANY joint polynomial moment jet read

The functionals act in native coordinates.Condition exact through A total,
including linear weights and factorials, no arbitrary factorization. This
will allow proof continuation to dual all-beam valuations (off-contact).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petals
open Tensor Analysis Function Filter Set MeasureTheory Native Pulse Nuclear Lattice
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d e k:ℕ} {V:Type}[Fintype V][DecidableEq V]
local notation "U"=> Cloud V
local notation "W"=> Wave V
section
variable (i:V) (j:Letter d)(x:Cloud V) (p:Wave V)
private abbrev onet : E4 →L[ℝ] Cloud V:=ContinuousLinearMap.single ℝ (fun _ : V=> E4) i
noncomputable def traceL : Body:=⟨(fork 1 x p).val ∘ (onet i), (show ContDiff ℝ ∞ _ from (show ContDiff ℝ ∞ (fork 1 x p).val from (fork 1 x p).property).comp (onet i).contDiff)⟩
lemma val_trace (u:E4): (traceL i x p).val u=p.val (x+Pi.single i u):=by change p.val (x+1 • _) = _;rw[one_smul]; rfl
lemma rows (t:E4)(n:ℕ):iteratedFDeriv ℝ n (traceL i x p).val t=(iteratedFDeriv ℝ n p.val (x+Pi.single i t)).compContinuousLinearMap (fun _=> onet i):=by
     rw [show iteratedFDeriv ℝ n (traceL i x p).val t= _ from (onet i).iteratedFDeriv_comp_right (lit (fork 1 x p) n) t (le_refl _)] -- rfl?
     rw [fork_at]; rfl
lemma cropped_spelling (x:Cloud V)(p:Wave V)(h:p∈chair k (Cloud V)): (lat j (fun v=>Pi.single i v) p).val x= ∑ u:Slots k, weights k j u * p.val (x+ Pi.single i (away (backward u))):=by
   have hc: traceL i x p ∈ chair k E4:=by
      change iteratedFDeriv ℝ _ _=0; funext y; rw [rows, show iteratedFDeriv ℝ (k+1) p.val=0 from h]; ext1 v; rfl
   simp_rw [← val_trace,← postal k j _ hc]
   rw [values,sample]; refine Finset.sum_congr rfl fun u _=> ?_; unfold Tensor.diagonal; rw [rows i x p,Pi.single_zero,add_zero];rfl
lemma at_lat (p:Wave V)(h:p∈chair k (Cloud V)): lat j (fun v=>Pi.single i v) p∈chair k (Cloud V):=by
    -- via stencil
    let f(u:Slots k):= weights k j u • fork 1 (Pi.single i (away (backward u))) p; apply (show lat j (fun v=> Pi.single i v) p=∑ u: Slots k, f u from ?_).symm ▸ ((chair _ _).sum_mem (f:=f) ?_ ) -- infer
    · intro u _; apply (chair _ _).smul_mem; change iteratedFDeriv ℝ _ _=0; funext y; rw [fork_at, show iteratedFDeriv ℝ _ p.val=0 from h];rfl
    apply Subtype.ext; funext x; rw [cropped_spelling i j x p h, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]; refine Finset.sum_congr rfl (fun u _=>?_); change _*_=(weights k j u) • p.val (_+(1:ℝ) • x);rw[one_smul,add_comm x]; rfl
end
section list
variable (s:V→ℕ) (z:∀ i:V,Letter (s i))
abbrev Forms (k:ℕ)(V:Type):= V→ Slots k
def effects (L:List V)(i:Forms k V):U:=fun j=> if j∈L then away (backward (i j)) else 0
def modes (L:List V)(p:Forms k V)(i:V):ℂ:= if i∈L then weights k (z i) (p i) else if p i=0 then 1 else 0
-- update eliminates singleton choice
lemma motor (L:List V)(p:Wave V)(h:p∈chair k (Cloud V))(he:L.Nodup)(x:Cloud V): (machine s z L p).val x= ∑ a:Forms k V,(∏ i:V,modes s z L a i)* p.val (x+effects L a) :=by
    induction L generalizing p x with
    | nil=> rw [Finset.sum_eq_single 0]; rotate_left
            · intro b _ hb; obtain ⟨i,hi⟩:= Function.ne_iff.mp hb; rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [modes,List.not_mem_nil,if_false]; rw [if_neg (show b i≠0 from hi)]),zero_mul]
            · simp
            rw [Finset.prod_eq_one (fun i _=>by simp [modes]),one_mul,show effects [] (0:Forms k V)=0 from funext fun x=>if_neg (by simp),add_zero];rfl
    | cons i L ih=>
       obtain ⟨hy,hN⟩:= List.nodup_cons.mp he
       rw [machine,LinearMap.comp_apply, ih _ (at_lat i (z i) p h) hN]; simp_rw [cropped_spelling i (z i) _ p h]
       let e:= Equiv.piSplitAt i (fun _=> Slots k); let I:=(j:{j:V//j≠i})→ Slots k; let w(b:I):=e.symm (0,b); let f':= weights k (z i)
       rw [←Equiv.sum_comp e.symm,← Equiv.sum_comp e.symm (g:=fun a:Forms k V=> (∏ i':V,modes s z (i::L) a i')*p.val (x+effects (i::L) a))] -- first rw maybe rhs too
       simp_rw [Fintype.sum_prod_type]; rw [Finset.sum_eq_single (a:= (0:Slots k))]; rotate_left
       · intro b _ hb; refine Finset.sum_eq_zero fun j _ => ?_; have hx:e.symm (b,j) i=b:= congr_arg Prod.fst (e.apply_symm_apply _); rw [Finset.prod_eq_zero (Finset.mem_univ i) (show modes _ _ L (e.symm (b,j)) i=0 by unfold modes; rw [if_neg hy, if_neg (fun h=>hb (hx.symm.trans h))]),zero_mul]
       · simp
       rw [Finset.sum_comm (s:=Finset.univ (α:= Slots k)) (t:=Finset.univ (α:=I))]; apply Finset.sum_congr rfl; intro b _; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _=>?_); let t:=e.symm (j,b); let u:= w b
       have hu : w b i=0:= congr_arg Prod.fst (e.apply_symm_apply _); have hv: t i=j:=congr_arg Prod.fst (e.apply_symm_apply _); have hF(y:V)(he:y≠i): t y= w b y:=by
          have ht := congr_arg Prod.snd (e.apply_symm_apply (j,b)); have hq:= congr_arg Prod.snd (e.apply_symm_apply (0,b)); exact congr_fun (ht.trans hq.symm) ⟨_,he⟩
       have hm : (∏ j:V,modes _ z L (w b) j)* f' j=∏ j:V,modes _ z (i::L) t j:=by
            rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), ← Finset.prod_erase_mul _ (modes s z (i::L) t) (Finset.mem_univ i),show modes _ z L (w b) i=1 from by simp [modes,hy,hu],show modes _ z (i::L) t i=f' j from by simp [modes,f',hv],mul_one]; congr 1; refine Finset.prod_congr rfl fun g hg=>?_ ; simp [modes,Finset.ne_of_mem_erase hg,hF g (Finset.ne_of_mem_erase hg)]
       rw [← mul_assoc,show _ * _ =∏ j:V,modes _ z (i::L) t j from hm]; rw [add_assoc,show effects L (u)+ Pi.single i (away (backward j))=effects (i::L) t from ?_];
       funext g; by_cases hz:g=i; · subst g; simp [effects,hv,hy]
       simp [effects,hz,Pi.single_eq_of_ne,hF g hz,u]
lemma all_ports (p:Wave V)(h:p∈chair k (Cloud V)) : (perform s z p).val 0= ∑ u:Forms k V,(∏ i:V,weights k (z i) (u i))*p.val (fun i=>away (backward (u i))):=by
    rw [perform, motor _ _ _ p h (Finset.nodup_toList ..)]; simp only [modes, show ∀ u:Forms k V,effects (Finset.univ (α:=V)).toList u=(fun i=> away (backward (u i))) from fun u=> funext fun i=>if_pos (by simp),Finset.mem_toList, Finset.mem_univ, if_true,zero_add]
end list
end YM.RG05Readout.Petals
