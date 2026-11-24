import YM.AlbaMS.Cutis.Fluent

/-!
# Single-color block notation, native full torus identity of arbitrary side

No bandwidth assumptions. Need Pin of directions with actual link-base sites
(half staggering position arithmetic in analytic application, not matrix shift here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Winter
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix
open Bric Loft Inlay Inlay.Net Odom Lattice
variable {n : Side}{G:Gauge}{E B X I R : Type*}
-- tensor helper applies all sizes. choose entrywise formulas.
section Socket
variable (I)[DecidableEq I][CommRing R]{A D:Matrix E B R} {P:Matrix B X R}
def chip (A:Matrix E B R) : Matrix (E×I) (B×I) R:= Matrix.of fun i j=> if i.2=j.2 then A i.1 j.1 else 0
lemma chip_one [DecidableEq E] : chip I (1:Matrix E E R)=1:=by ext ⟨i,x⟩ ⟨j,y⟩; by_cases h:x=y<;>simp [chip,h,Matrix.one_apply,and_comm]
lemma chip_zero : chip I (0:Matrix E B R)=0:=by ext; simp [chip]
lemma chip_add : chip I (A+D)=chip I A+chip I D:= by ext; simp [chip]; split<;> first|rfl|exact (zero_add (0:R)).symm
lemma chip_scale (c:R): chip I (c • A)=c • chip I A:=by ext; simp [chip,mul_ite]
lemma chip_sub : chip I (A-D)=chip I A-chip I D:=by simp_rw [sub_eq_add_neg,← neg_one_smul R D,chip_add,chip_scale,neg_one_smul]
lemma chip_t : (chip I A)ᵀ= chip I Aᵀ:=by ext; simp [chip,eq_comm]
variable [Fintype I][Fintype B]
lemma chip_prod : chip I A*chip I P=chip I (A*P):=by ext ⟨a,i⟩ ⟨b,j⟩; by_cases h:i=j<;> simp [Matrix.mul_apply,chip,h,Fintype.sum_prod_type,mul_ite,ite_mul]
end Socket
abbrev Tong (n:Side):= Matrix (Arm n) (Vtx n) ℝ
abbrev Dir (n:Side):=Matrix (Arm n) (Arm n) ℝ
variable (n)(i j k:Axis)
def mouth : Tong n:= Matrix.of fun x y=> if (y,i)=x then 1 else 0
def pump (A: Cell n) : Dir n:=chip Axis A
lemma cheeks {X:Type*} (A:Matrix X (Arm n) ℝ)(x y):(A*mouth n i) x y=A x (y,i):=by simp [mouth,Matrix.mul_apply,mul_ite]
lemma cheeks_left {X: Type*}(A:Matrix (Arm n) X ℝ)(x y): ((mouth n i)ᵀ*A) x y=A (x,i) y:=by nth_rw 1 [← transpose_transpose A]; rw [← transpose_mul]; exact cheeks ..
lemma mouth_orth : (mouth n i)ᵀ * mouth n j=if i=j then 1 else 0:=by
  ext x y; rw [cheeks]; unfold mouth; by_cases h:i=j<;> simp [Matrix.one_apply,h]
lemma mouth_complete : (∑ i:Axis,mouth n i*(mouth n i)ᵀ)=1:=by
  ext ⟨x,i⟩ ⟨y,j⟩; rw [Matrix.sum_apply, Matrix.one_apply]; simp_rw [Matrix.mul_apply]; unfold mouth; simp only [Matrix.of_apply, Matrix.transpose_apply,Prod.mk.injEq, ite_mul, mul_ite, mul_one, one_mul,MulZeroClass.zero_mul]; by_cases hv:x=y<;>by_cases hk:i=j<;>simp [ite_and,hv,hk] <;> aesop
lemma pump_by (A: Cell n): pump n A* mouth n i= mouth n i * A:=by ext ⟨x,j⟩ y; rw [cheeks]; unfold pump chip mouth; simp [Matrix.mul_apply,ite_mul,ite_and,eq_comm]
lemma pump_to (A:Cell n): (mouth n i)ᵀ * pump n A = A* (mouth n i)ᵀ:=by
  nth_rw 1 [← show (pump n Aᵀ)ᵀ = pump n A by simp only [pump,chip_t,transpose_transpose]]; rw [← transpose_mul, pump_by,transpose_mul,transpose_transpose]
lemma stalk (A:Cell n): (∑ i:Axis,mouth n i*A*(mouth n i)ᵀ)=pump n A:=by simp_rw [← pump_by, Matrix.mul_assoc, ← Matrix.mul_sum,mouth_complete,Matrix.mul_one]

def bound (n:Side): Tong n:= ∑ i:Axis,mouth n i * del n i
lemma eyebrow : (mouth n i)ᵀ*bound n=del n i:=by unfold bound; rw [Matrix.mul_sum]; simp_rw [← Matrix.mul_assoc,mouth_orth]; simp [ite_mul]
lemma flash (x y : Vtx n): bound n (x,i) y= (del n i) x y:=by rw [← eyebrow]; exact (cheeks_left n i (bound n) x y).symm
-- locate gradient interactions from lap moments
lemma q_sc : (bound n)ᵀ*bound n=lap n:=by nth_rw 1 [bound];rw [transpose_sum,Matrix.sum_mul,lap]; exact Finset.sum_congr rfl fun i _=> by rw [transpose_mul, Matrix.mul_assoc, eyebrow]
lemma bound_mean : bound n * mean n=0:=by simp_rw [bound,Matrix.sum_mul,Matrix.mul_assoc, mean_del,Matrix.mul_zero,Finset.sum_const_zero]
lemma mean_bound : pump n (mean n) * bound n=0:=by simp_rw [bound,Matrix.mul_sum, ← Matrix.mul_assoc, pump_by, Matrix.mul_assoc, del_mean, Matrix.mul_zero, Finset.sum_const_zero]
lemma pump_normal (A:Cell n)(h:∀ i:Axis,Commute A (del n i)): pump n A*bound n=bound n*A:=by unfold bound; rw [Matrix.mul_sum,Matrix.sum_mul]; exact Finset.sum_congr rfl (fun i _=> by rw [← Matrix.mul_assoc,pump_by,Matrix.mul_assoc, show A*_=_ from h i,Matrix.mul_assoc])
lemma pump_lap : pump n (lap n)*bound n=bound n * lap n:=pump_normal n _ (commute_lap n)
lemma pump_green : pump n (green n)*bound n=bound n * green n:=pump_normal n _ (green_del n)
end YM.MSBar.Cutis.Winter
