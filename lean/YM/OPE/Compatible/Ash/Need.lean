import YM.OPE.Compatible.Ash.Hush
/-!
# Real unscaled line hierarchy, alias-exact
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full
open scoped BigOperators Classical ContDiff
variable {n m:Side}
def rye (g:Ratio n m):Ratio g.count m:=⟨n,g.exact_size.trans (mul_comm ..)⟩
lemma rye_sig (g:Ratio n m)(p: Site m)(b:Site g.count): char p ((rye g).embed b)=char (g.residue p) b:=by -- choose cover
   obtain ⟨x,rfl⟩:∃ x,wrap m x=p:=⟨_,wrap_lift p⟩
   rw [Pert.Full.swap, embed_sig,g.residue_wrap, Pert.Full.swap]
lemma rye_coin (g:Ratio n m)(p:Site n): (g.count.val:ℂ)^4*topWeight m (g.embed p)=topWeight n p:=by
   unfold topWeight; rw [embed_ret, g.exact_size]; push_cast; field_simp
lemma contourC (g:Ratio n m)(a:Cover): toroid (wrap n a)=∑ p:Site g.count,toroid ((rye g).embed p+wrap m a):=by
   unfold toroid; conv_rhs=>rw [Finset.sum_comm]
   simp_rw [char_add, ←Finset.mul_sum, ← Finset.sum_mul,rye_sig,scan] -- remove surpl
   rw [←Equiv.sum_comp g.splitSites.symm]; rw [Fintype.sum_prod_type]
   apply Finset.sum_congr rfl; intro p hp; rw [Finset.sum_eq_single (0:Site g.count)]
   · simp_rw [show g.splitSites.symm (p,0)=g.embed p from by change g.embed p+wrap m (Lattice.lift (0:Site g.count))=_; rw [show Lattice.lift (0:Site g.count)=0 from funext (fun i=>ZMod.valMinAbs_zero ..),map_zero,add_zero],g.residue_embed,if_true, embed_sig]; rw [← mul_assoc,mul_comm (topWeight m (g.embed p)),rye_coin]
   · intro j _ hh; rw [show g.residue (g.splitSites.symm (p,j))=_ from g.assemble_res (p,j)]; simp only [if_neg hh,zero_mul,mul_zero] -- reduce
   simp
-- real∆
def mildX (D:List Axis)(x:Site n):ℝ:= (joint 1 D x).re
lemma full_X (D:List Axis)(x:Site n)(h:ℝ)(hh:0<h): mildX D x=h^(D.length+2)*(joint h D x).re:=by
   unfold mildX; have he:joint 1 D x=(h^(D.length+2):ℝ) • joint h D x:=by unfold joint; simp only [Complex.ofReal_one,one_zpow,one_mul]; rw [show -((D.length:ℤ)+2)= -((D.length+2:ℕ):ℤ) from by omega, zpow_neg,zpow_natCast,Complex.real_smul,Complex.ofReal_pow,← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hh.ne')),one_mul]
   erw [he,Complex.smul_re];rfl
lemma mild_tip (x:Site n): mildX [] x=(toroid x).re:=by unfold mildX joint toroid; simp only [Complex.ofReal_one, one_zpow,one_mul,claw,List.map_nil,List.prod_nil,mul_one]; simp_rw [mul_comm (char _ x)]
lemma mild_more (x:Site n)(D:List Axis)(i:Axis): mildX (i::D) x=mildX D (x+step i)-mildX D x:=by
    have he: joint 1 (i::D) x=joint 1 D (x+step i)-joint 1 D x:=by
       unfold joint; simp only [Complex.ofReal_one,one_zpow,one_mul,claw,List.map_cons,List.prod_cons]; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro p hp; rw [char_add]; ring
    simp only [mildX,he,Complex.sub_re]
lemma aliasX (g:Ratio n m)(a:Cover)(D:List Axis): mildX D (wrap n a)=∑ p:Site g.count,mildX D ((rye g).embed p+wrap m a):=by
    induction D generalizing a with
    | nil=>simp only [mild_tip,contourC g a,Complex.re_sum]
    | cons i t ih=>simp only [mild_more]; simp_rw [show wrap n a+step i=wrap n (a+step i) from by rw [map_add,wrap_step], ih]; rw [← Finset.sum_sub_distrib]; congr 1; ext p;rw [add_assoc,map_add,wrap_step]
end YM.OPE.Balsam
