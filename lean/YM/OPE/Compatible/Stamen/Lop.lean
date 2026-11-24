import YM.OPE.Compatible.Stamen.Hill
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
section
lemma warper (u:Fin k→fieldX I)(p:Script I k)(a:Equiv.Perm (Fin k)): wholeX (swing a p) u=wholeX p (u ∘ a):=by
       let f:Page I k ≃ Page I k:=Equiv.arrowCongr a.symm (Equiv.refl _); unfold wholeX; rw [← f.tsum_eq (fun i=>p i *wordX (u ∘ a) i)]; apply tsum_congr;intro i;change p (f i)*_= _; apply congr_arg; exact (Equiv.prod_comp a (fun j=>u j (i j))).symm
lemma gpop (v w:fieldX I)(sA:Fin k)(p:Script I k)(j:Fin k)(hp:p.sorted): wholeX p (mark v w sA)=wholeX p (mark v w j):=by
       let W:=Equiv.swap sA j; rw [← hp W, warper, hp]; apply congr_arg; unfold mark; rw [update_comp_equiv]; simp [W]; rfl
lemma twirl (p:Script I (k+2))(hp:p.sorted)(v w:fieldX I)(i j:Fin (k+2))(ht:i≠j): wholeX p (markP v w i j)=wholeX p (Fin.cons w (Fin.cons w (fun _=>v))):=by -- choose permutation
       let sA:=Equiv.swap 0 i; let h:= sA.symm j; have hh:h≠0:=by intro he; apply ht; have hz:= sA.apply_symm_apply j; change sA h=_ at hz; rw[he,show sA 0=i from Equiv.swap_apply_left ..] at hz; exact hz
       let r':=(Equiv.swap (1:Fin (k+2)) h); let q:=r'.trans sA; have hu:q 0=i:=by rw[show q 0=sA (r' 0) from rfl, show r' 0=0 from Equiv.swap_apply_of_ne_of_ne (Ne.symm (Fin.succ_ne_zero (0:Fin (k+1)))) hh.symm]; exact Equiv.swap_apply_left ..
       have hy:q 1=j:=by rw[show q 1=sA (r' 1) from rfl, show r' 1=h from Equiv.swap_apply_left ..]; exact sA.apply_symm_apply _
       rw [← (show _=wholeX p (markP v w i j) from congr_arg (fun z=>wholeX z _) (hp q)), warper]; apply congr_arg; ext1 l; refine Fin.cases ?_ (fun i'=> Fin.cases ?_ (fun j'=>?_) i') l
       · unfold markP mark; rw[Function.comp_apply,hu,update_of_ne ht,update_self, Fin.cons_zero]
       · simp[markP, hy]
       have hx: j'.succ.succ≠(1:Fin (k+2)):=Fin.succ_inj.not.mpr (Fin.succ_ne_zero _); simp only[Function.comp_apply,markP,Fin.cons_succ]; rw[update_of_ne (show q j'.succ.succ≠j from fun he=>hx (q.injective (he.trans hy.symm))),mark,update_of_ne (show q j'.succ.succ≠i from fun he=> Fin.succ_ne_zero _ (q.injective (he.trans hu.symm)))]
def Carve (v w:fieldX I) (p:Script I k):ℝ:=∑ i,wholeX p (mark v w i)
def Carve2 (v w:fieldX I)(p:Script I k):ℝ:=∑ i,∑ j∈ univ.erase i, wholeX p (markP v w i j)
lemma pillar (p:Script I (k+1))(hp:p.sorted)(v w:fieldX I): Carve v w p=((k+1:ℕ):ℝ)*wholeX p (Fin.cons w (fun _=>v)):=by
       unfold Carve; simp_rw [show ∀ i: Fin (k+1), wholeX p (mark v w i)=wholeX p (mark v w 0) from fun i=> gpop v w i p 0 hp, sum_const, card_univ,Fintype.card_fin,nsmul_eq_mul]; apply congr_arg; apply congr_arg; unfold mark; ext1 i; refine Fin.cases ?_ (fun j=>?_) i<;>simp
lemma pillar2 (p:Script I (k+2))(hp:p.sorted)(v w:fieldX I): Carve2 v w p=((k+2:ℕ):ℝ)*((k+1:ℕ):ℝ)*wholeX p (Fin.cons w (Fin.cons w (fun _=>v))):=by
       let S:=wholeX p (Fin.cons w (Fin.cons w (fun _=>v))); have ht(i:Fin (k+2)):(∑ j∈ univ.erase i,wholeX p (markP v w i j))=((k+1:ℕ):ℝ)*S:=by rw [sum_congr rfl (g:=fun _=>S) (fun j hj=>twirl p hp v w i j (ne_of_mem_erase hj).symm)]; simp [nsmul_eq_mul]
       unfold Carve2; simp_rw [ht]; rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc]
end
end YM.OPE.Silt.Phere
