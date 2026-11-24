import YM.AveragedStep.Recursion.Product
import Mathlib.Algebra.MvPolynomial.PDeriv
/-!
# Real Wick normalization

Method of YM.Next.Rank.Normal.{make,blend} adapted from complex
scheme to compensated real covariance signs. No rank requirement.
For conditional internal lattice steps only. Not a call to any heat
normalization, or to the physical correlation field.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD
open Filter Function Lattice RG Wilson Precision Tree Set
open scoped Topology BigOperators Classical
namespace TreeHeat
open MvPolynomial
abbrev Pol (I : Type*) := MvPolynomial I ℝ
variable {I:Type*}

def glide(i:I):Derivation ℝ (Pol I) (Pol I):=pderiv i
lemma glide_many(i:I)(p q:Pol I):glide i (p*q)=glide i p*q+p*glide i q:=pderiv_mul
lemma glide_X(i j:I):glide i (X j:Pol I)=if j=i then 1 else 0:=by by_cases h:j=i <;> simp [glide,h]
lemma glide_comm (i j:I)(p:Pol I):glide i (glide j p)=glide j (glide i p):=by
 induction p using MvPolynomial.induction_on with
 | C a=> simp [glide]
 | add p q h k=> simp only [_root_.map_add,h,k]
 | mul_X p t h =>
   simp only [_root_.map_add,glide_many]; rw [h]; simp only [glide_X]; split_ifs <;> simp [glide]; ring

structure Frost (I:Type*) where
  cov:I→I→ℝ
  swap i j:cov i j=cov j i
variable (F:Frost I)
variable [Fintype I]

def edge (F:Frost I)(i:I): Pol I →ₗ[ℝ] Pol I:=∑ j,F.cov i j • (glide j).toLinearMap
lemma edge_eq(i:I)(p:Pol I):edge F i p=∑ j,F.cov i j • glide j p:=by simp [edge,LinearMap.sum_apply]
lemma skating (i j:I)(p:Pol I):glide j (edge F i p)=edge F i (glide j p):=by
 rw [edge_eq,edge_eq,_root_.map_sum]; simp_rw [Derivation.map_smul,glide_comm j]
lemma edge_prod (i j:I)(p:Pol I): edge F i (X j*p) = X j*edge F i p+F.cov i j • p:=by
 rw [edge_eq,edge_eq,Finset.mul_sum]; simp only [glide_many,smul_add,glide_X,ite_mul,one_mul,zero_mul,Finset.sum_add_distrib, mul_smul_comm]
 rw [add_comm]; congr 1
 rw [Finset.sum_eq_single j]; · rw [if_pos rfl]
 · intro b hb he; simp only [if_neg (Ne.symm he),smul_zero]
 simp

def sky (i:I): Module.End ℝ (Pol I) := LinearMap.mulLeft ℝ (X i)+edge F i
lemma sky_eq (i:I)(p): sky F i p= X i*p+edge F i p:=rfl
lemma commute (i j:I): Commute (sky F i) (sky F j):=by
 apply LinearMap.ext; intro p
 change sky F i (sky F j p)=sky F j (sky F i p)
 simp only [sky_eq,_root_.map_add,edge_prod,F.swap i j]
 have h:edge F i (edge F j p)=edge F j (edge F i p):=by
    simp_rw [edge_eq F i,skating F,_root_.map_sum,_root_.map_smul]
 rw [h]; ring
private abbrev Room(F:Frost I):= Algebra.adjoin ℝ (Set.range (sky F))
open scoped IsMulCommutative in
local instance : CommSemiring (Room F):=by
 have h:=Algebra.isMulCommutative_adjoin (s:=Set.range (sky F)) ℝ (by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩; exact commute F i j)
 infer_instance
def room (F:Frost I):Pol I→ₐ[ℝ] Module.End ℝ (Pol I):=(Room F).val.comp (aeval (fun i=>(⟨sky F i,Algebra.subset_adjoin ⟨i,rfl⟩⟩:Room F)))
lemma room_X (i:I):room F (X i)=sky F i:=by simp only [room,AlgHom.comp_apply,aeval_X];rfl
/-- Real contraction exponential in the covariance F. -/
def squash (F:Frost I) : Module.End ℝ (Pol I):=((LinearMap.applyₗ (R:=ℝ)) 1).comp (room F).toLinearMap
lemma squash_eq(p):squash F p=(room F p) 1:=rfl
lemma unit : squash F 1=1:=by rw [squash_eq,map_one (room F)]; rfl
lemma bulge(i:I)(p:Pol I):squash F (X i*p)=X i*squash F p+ edge F i (squash F p):=by rw [squash_eq,map_mul (room F),room_X]; rfl
@[simp] lemma squash_C (c:ℝ):squash F (MvPolynomial.C c)= MvPolynomial.C c:=by rw [show (MvPolynomial.C c:Pol I)= c • (1:Pol I) from (by rw [← C_mul',mul_one]),map_smul,unit]
lemma squash_glide(i:I)(p:Pol I):glide i (squash F p)=squash F (glide i p):=by
 induction p using MvPolynomial.induction_on with
 | C c=>simp [squash_C,glide]
 | add p q h hp=>simp only [_root_.map_add,h,hp]
 | mul_X p j h=>
   rw [mul_comm p,bulge,_root_.map_add,glide_many,glide_many,skating,h, _root_.map_add,bulge,glide_X]; split_ifs <;> simp [add_assoc]
def shine (m:I→ℝ): Pol I→ₗ[ℝ] ℝ := (MvPolynomial.aeval m).toLinearMap.comp (squash F)
lemma shine_one (m:I→ℝ):shine F m 1=1:=by change (aeval m) (squash F _)=_; rw [unit,map_one]
lemma shine_wick (m:I→ℝ)(i:I)(p:Pol I):shine F m (X i*p)=m i*shine F m p+∑ j,F.cov i j * shine F m (glide j p):=by
 change aeval m (squash F (X i*p)) = _ ; rw [bulge,_root_.map_add,map_mul,aeval_X,edge_eq]; simp_rw [squash_glide,_root_.map_sum,_root_.map_smul,smul_eq_mul]; rfl
end TreeHeat
end YM.AveragedStep.SD
