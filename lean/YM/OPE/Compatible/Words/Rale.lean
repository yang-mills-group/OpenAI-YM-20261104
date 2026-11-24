import YM.OPE.Compatible.Words.Verse
/-!
# Exponential reading at all ranks
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt
open MeasureTheory Function Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {I J:Type}[Fintype I]{n k m d:ℕ}
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](A:Law E)
variable (Z:E→L[ℝ] PAD I)
variable (x:PAD I) (t:ℝ)
local notation "P!"=> PAD I
-- fder
lemma vial (p:Pole P! 1)(h: Tensor.Sym p): HasDerivAt (fun u:ℝ=>A.average μ (oval Z x u p)) 0 t:=by
     let f(u:ℝ×E):= oval Z x u.1 p u.2; convert! hotrod μ A f (ovalQ Z x p) t using 1; let q(i:E):=Tensor.diagonal (p.curryLeft (Z i)) (x+t • Z i); have hp(i:E): deriv (fun u:ℝ=> f (u,i)) t=q i:=by rw [show deriv _ t= _ from rays x Z t p h i]; rw [show ((0+1:ℕ):ℝ)=(1:ℝ) by norm_num,one_mul]
     simp_rw [hp]; symm; apply colorful _ _ _ (show Bond q from by convert! reel f (ovalQ Z x p) t using 1; exact (funext hp).symm) fun i=>?_ ; unfold q; rw [map_neg,map_neg]; unfold Tensor.diagonal; rw [_root_.neg_apply, show (fun _ :Fin 0=> x+t • -Z i)=(fun _=>x+t • Z i) from Subsingleton.elim ..] -- neg
omit [FiniteDimensional ℝ E][BorelSpace E][μ.IsAddHaarMeasure] in lemma baseX (p:Pole P! 0): HasDerivAt (fun u:ℝ=>A.average μ (oval Z x u p)) 0 t:=by convert! hasDerivAt_const t (A.average μ (fun _=> Tensor.diagonal p x)) using 1; congr! 2 with i; ext1 v; exact congr_arg p (Subsingleton.elim ..)
-- sum
abbrev Strike {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F] (n:ℕ)(p:Song F)(x:F):ℝ:= ∑ i∈range (n+1),Tensor.diagonal (p i) x -- need type lemma
noncomputable def callP (n:ℕ)(x:P!): (Song P!) →ₗ[ℝ] ℝ where
     toFun p:= Strike n p x
     map_add' a b:=by simp only [Strike,Pi.add_apply,Tensor.diagonal,_root_.add_apply,Finset.sum_add_distrib]
     map_smul' a b:=by simp only [Strike,Pi.smul_apply,Tensor.diagonal,_root_.smul_apply]; exact (Finset.smul_sum ..).symm -- may reduce algebra map
lemma starP (p:Song P!)(hp:p ∈ harmon P! k)(he:k≤d) (x:P!):Strike k p x=Strike d p x:=Finset.sum_subset (range_mono (Nat.add_le_add_right he 1)) fun i _ hi=>by rw [(show ∀i,i>k→p i=0 from hp.1) _ (Nat.not_lt.mp fun h=>hi (mem_range.mpr h))]; rfl
lemma reelA (p:Song P!): A.average μ (fun v:E=> Strike n p (x+t • Z v))=∑ i∈range (n+1), A.average μ (oval Z x t (p i)):=by rw [show (fun v:E=> Strike n p (x+t • Z v))= (∑ i∈range (n+1),oval Z x t (p i)) from funext (fun i=> by rw [Finset.sum_apply]), science μ A _ _ fun _ _=> levied ..]
lemma pet (p:Song P!)(h:p∈ harmon P! n): HasDerivAt (fun s:ℝ=> A.average μ (fun v:E=> Strike n p (x+s • Z v))) (t*A.average μ (fun v:E=>Strike (n-1) (opus (chamber A Z) p) (x+t • Z v))) t:=by
       let D:=opus (chamber A Z); let f (i:ℕ)(t:ℝ):=A.average μ (oval Z x t (p i)); let g(i:ℕ):= A.average μ (oval Z x t (D p i)); have hp(i):Tensor.Sym (p i):=h.2 i; have ht (i:ℕ):HasDerivAt (f (i+2)) (t*g i) t:= aroma μ A x Z t _ (hp _)
       simp_rw [reelA μ A]
       change HasDerivAt (fun s => ∑ i∈range (n+1),f i s) (t*∑ i∈range (n-1+1),g i) t
       have he(i:ℕ)(hx:i+2>n):g i=0:=by
            unfold g; rw [show D p i= 0 from ?_, show oval Z x t (0:Pole P! i)=(fun _=>0) from rfl,singleConst]; change wind _ • Semester (chamber A Z) (p (i+2))= _; rw [(show ∀ i, i>n→p i=0 from h.1) (i+2) hx,semZ, smul_zero]
       have hz :HasDerivAt (f 0) 0 t:=baseX μ A Z x t _; cases n with
       | zero=> simp_rw [Nat.zero_sub, Nat.zero_add, sum_range_one, he 0 (by omega),mul_zero]; exact hz
       | succ n=>
           have hh:HasDerivAt (f 1) 0 t:=vial μ A Z x t (p 1) (hp _)
           have hp:= HasDerivAt.fun_sum (u:=range n) (A:=fun i s=>f (i+2) s) (fun i _=>ht i)
           convert! (hp.add hh|>.add hz) using 1
           · funext i; rw [sum_range_succ',sum_range_succ']; rfl
           rw [Nat.add_sub_cancel,sum_range_succ,he n (by omega),add_zero,mul_sum,add_zero,add_zero]
end YM.OPE.Silt
