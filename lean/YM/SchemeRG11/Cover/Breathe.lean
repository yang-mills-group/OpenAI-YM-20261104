import YM.SchemeRG11.Cover.Heat
import YM.Next.RANK.GaussTags
/-! Open legs. Wick substitution in arbitrary rings; compatible with
 complex Normal. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Haze
open MvPolynomial
open scoped Classical
variable {R S J I B : Type*} [CommRing R] [CommRing S]
lemma vent_zero (p : Paper I R): vent 0 p=0:=by
 have he: vent (0 : I→R)=0:=by ext i; simp [vent]
 rw [he];rfl
lemma vent_add (u v:I→R)(p : Paper I R): vent (u+v) p=vent u p+vent v p:=by
 have he : vent (u+v)=vent u+vent v:=by ext i; simp [vent,Derivation.add_apply]
 rw [he];rfl
lemma vent_smul (u:I→R)(c:R)(p:Paper I R): vent (c • u) p= c • vent u p:=by
 -- SMul deriv
 induction p using MvPolynomial.induction_on with
 | C => simp only [vent_C, smul_zero]
 | add a b ha hb=> rw [map_add,map_add,ha,hb,smul_add]
 | mul_X a i h=> rw [vent_x,vent_x,h,smul_add,Pi.smul_apply,smul_eq_mul,smul_smul,mul_smul_comm]
lemma vent_neg (z:I→R)(p : Paper I R): vent (-z) p= -vent z p:=by simpa using vent_smul z (-1) p

abbrev Stem (I R:Type*) [Zero R] := I →₀ R
abbrev leaf : Stem I R→ₗ[R] Paper I R:= Finsupp.linearCombination R MvPolynomial.X
abbrev sense (z:I→R) : Stem I R→ₗ[R] R:= Finsupp.linearCombination R z
lemma taste (z:I→R) (v : Stem I R) : vent z (leaf v)=MvPolynomial.C (sense z v):=by
 induction v using Finsupp.induction_linear with
 | zero => rw [map_zero,map_zero,map_zero,map_zero]
 | add a b ha hb => rw [map_add,map_add,map_add,map_add,ha,hb]
 | single i b=> simp only [sense,leaf,Finsupp.linearCombination_single,(vent z).map_smul]; rw [vent, mkDerivation_X, smul_eq_mul, MvPolynomial.smul_eq_C_mul,map_mul]
lemma realTaste (z:I→R) (v:Stem I R): aeval z (leaf v)=sense z v:=by change (aeval z).toLinearMap _=_; rw [leaf,LinearMap.map_finsupp_linearCombination]; exact congrArg (fun f=> Finsupp.linearCombination R f v) (funext (fun i=>aeval_X ..))
lemma taste_prod (s:Finset J) (z:I→R) (v:J→Stem I R): vent z (∏ i∈s,leaf (v i))=∑i∈s,sense z (v i) • ∏ j∈s.erase i,leaf (v j):=by
 induction s using Finset.induction_on with
 | empty=> simp only [Finset.prod_empty,(vent z).map_one_eq_zero,Finset.sum_empty]
 | insert i s hi ih=>
  simp_rw [Finset.prod_insert hi,vent_l,taste,ih, Finset.sum_insert hi,Finset.erase_insert hi,Finset.mul_sum,MvPolynomial.smul_eq_C_mul]
  rw [add_comm]; congr 1
  · rw [mul_comm]
  apply Finset.sum_congr rfl; intro j hj; rw [Finset.erase_insert_of_ne (fun (h:i=j)=>hi (h ▸ hj)), Finset.prod_insert (fun he=>hi (Finset.mem_of_mem_erase he))]; ring
namespace Dose
variable (D:Dose I R)
def windfall : Stem I R→ₗ[R] (I→R):=Finsupp.linearCombination R D.pulse
@[simp] lemma single_wind (i:I) : D.windfall (Finsupp.single i 1)=D.pulse i:=by rw [windfall,Finsupp.linearCombination_single,one_smul]
def bed (u v:Stem I R):= sense (D.windfall u) v
lemma bed_comm (u v:Stem I R): bed D u v=bed D v u:=by
 unfold bed windfall sense; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul, Finset.mul_sum]
 rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [D.beats j i]; ring
lemma flow (z:I→R)(v:Stem I R)(p:Paper I R): vent z (leaf v*p)=leaf v*vent z p+sense z v • p:=by rw [vent_l,taste,mul_comm p,MvPolynomial.smul_eq_C_mul]
lemma zephyr (v:Stem I R)(p:Paper I R): D.heat (leaf v*p)=leaf v*D.heat p + vent (D.windfall v) (D.heat p):=by
 induction v using Finsupp.induction_linear with
 | zero=> rw [map_zero,map_zero,zero_mul,zero_mul,map_zero,vent_zero,add_zero]
 | add a b ha hb=> rw [map_add,map_add,vent_add,add_mul,add_mul,map_add,ha,hb]; abel
 | single i b=>simp only [leaf,windfall,Finsupp.linearCombination_single,smul_mul_assoc,mul_comm (X i), map_smul]; rw [heat_x,smul_add,vent_smul,mul_comm (D.heat p)]
lemma lit (v:Stem I R) : D.heat (leaf v)=leaf v:=by
 have he := D.zephyr v 1; rw [mul_one,heat_one, mul_one, Derivation.map_one_eq_zero, add_zero] at he; exact he
lemma release_leaf (v: Stem I R)(p:Paper I R): D.avg (leaf v*p)=D.avg (vent (D.windfall v) p):=by
 rw [avg_def, D.zephyr,D.wind,map_add,map_mul,realTaste, show (sense (fun _:I=>(0:R))) v=0 by simp [sense,Finsupp.linearCombination_apply,Finsupp.sum], zero_mul,zero_add,avg_def]
lemma zeph_neg (v:Stem I R) (p:Paper I R): D.neg.heat (leaf v*p)=leaf v*(D.neg.heat p) - vent (D.windfall v) (D.neg.heat p):=by
 have he : D.neg.windfall v= - D.windfall v:=by funext i; unfold windfall neg; simp [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply, mul_neg]
 rw [D.neg.zephyr,he,vent_neg,sub_eq_add_neg]
end Dose
abbrev vary (L : J→Stem I R) := (aeval (fun i=>leaf (L i)) : Paper J R→ₐ[R] Paper I R)
lemma varyV (L : J→Stem I R) (z : I→R) (p:Paper J R): aeval z (vary L p)=aeval (fun i=> sense z (L i)) p:=by
 apply DFunLike.congr_fun (f:=(aeval z).comp (vary L)); ext i; rw [AlgHom.comp_apply,vary, aeval_X,aeval_X]; apply realTaste
lemma vary_zero (L : J→Stem I R) (p:Paper J R): aeval (fun _:I=>(0:R)) (vary L p)=aeval (fun _:J=>(0:R)) p:=by rw [varyV]; simp [sense,Finsupp.linearCombination_apply,Finsupp.sum]
lemma vary_X (L : J→Stem I R) (i:J): vary L (X i)=leaf (L i):=aeval_X ..
lemma vary_C (L : J→Stem I R) (c:R): vary L (MvPolynomial.C c)=MvPolynomial.C c := (vary L).commutes c
lemma varyVent (L : J→Stem I R) (z:I→R)(p:Paper J R): vent z (vary L p)=vary L (vent (fun i=>sense z (L i)) p):=by
 induction p using MvPolynomial.induction_on with
 | C=> rw [vary_C,vent_C,vent_C,map_zero]
 | add a b ha hb=> rw [map_add,map_add,ha,hb,map_add,map_add]
 | mul_X a i h=>
   rw [vent_x,map_mul (vary L),vary_X, map_add,map_smul,map_mul (vary L),vary_X, mul_comm, Dose.flow z,h,add_comm]
namespace Dose
variable (D:Dose I R)
def pull (L : J→Stem I R): Dose J R:= ⟨fun i j=>D.bed (L i) (L j),fun i j=>D.bed_comm (L i) (L j)⟩
lemma light (L : J→Stem I R) (p:Paper J R): D.heat (vary L p)=vary L ((D.pull L).heat p):=by
 induction p using MvPolynomial.induction_on with
 | C=> rw [vary_C,D.heat_C,heat_C,vary_C]
 | add a b ha hb=> rw [map_add,map_add,map_add,map_add,ha,hb]
 | mul_X a i h=> rw [heat_x,map_add,map_mul (vary L),map_mul (vary L),vary_X,mul_comm (vary L a),D.zephyr,h,varyVent];rfl
lemma night (L : J→Stem I R) (p:Paper J R): D.neg.heat (vary L p)=vary L ((D.pull L).neg.heat p):= by calc
 _=D.neg.heat (vary L ((D.pull L).heat ((D.pull L).neg.heat p))) := by rw [reverse]
 _=_:=by rw [←light,opposite]
lemma colour (L : J→Stem I R) (p:Paper J R): D.avg (vary L p)=(D.pull L).avg p:=by rw [avg_def,light,vary_zero,avg_def]
-- adapter
open YM.Next.Rank.Normal
variable (E:Dose J ℂ)
def toNormal : Symmetric J := ⟨E.pulse,E.beats⟩
lemma agrees(p:Paper J ℂ): E.heat p=milk E.toNormal p:=by
 induction p using MvPolynomial.induction_on with
 | C a=> rw [heat_C, fine]
 | add a b ha hb=> rw [map_add,map_add,ha,hb]
 | mul_X a i h=> rw [heat_x,h,mul_comm a, feeds]; rfl
lemma blend_eq (p:Paper J ℂ): E.avg p=blend E.toNormal 0 p:=by rw [avg_def,agrees];rfl
end Dose
end YM.SchemeRG11.Haze
