import YM.X.Try.Spire
/-!
# Oriented area forms. e conventions E:E.TRing; use rational internal twice-un-normalized (proof computation r basis = std times √2). proof of multiplication and formula for p determinant sign.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Maxwell Function Filter Set Matrix Lattice MeasureTheory
open scoped Topology Classical
variable {G:Gauge} {V:Type*}
abbrev Tet := Fin 3
abbrev Axes (V:Type*):= Axis→Axis→V
-- signs; Area ε tensor cyclic stencil
local notation "T"=> Fin 3
def form (t:ℝ)(i:Tet)(a b:Axis) : ℝ :=
  match i.val,a.val,b.val with
  | 0,0,1 => 1 | 1,0,2 => 1 | 2,0,3 => 1
  | 0,2,3 => t | 1,1,3 => -t | 2,1,2 => t
  | 0,1,0 => -1 | 1,2,0 => -1 | 2,3,0 => -1
  | 0,3,2 => -t | 1,3,1 => t | 2,2,1 => -t
  | _,_,_ => 0
def mn (i:Tet):= form (-1) i
def ps (i:Tet):= form 1 i
def loop (i:Tet): T:= 
  match i.val with|0=>⟨1,by decide⟩|1=>⟨2,by decide⟩|_=>⟨0,by decide⟩
def ℓ (i:Tet):= loop (loop i)
lemma loop₂ (i:T): loop (ℓ i)=i:= by fin_cases i<;>decide
lemma loop'₂ (i:T): ℓ (loop i)=i:= loop₂ ..
lemma loop₁ (i:T):loop i ≠ i:= by fin_cases i<;>decide
lemma ℓ₁ (i:T):ℓ i ≠ i:= by fin_cases i<;>decide
lemma ℓ₂ (i:T): ℓ i ≠ loop i:= by fin_cases i<;>decide
def η (i j k:T):ℝ:= if loop i=j∧ℓ i=k then 1 else if loop i=k∧ℓ i=j then -1 else 0
lemma fi3 : (2 : Tet)=⟨2,by decide⟩ :=rfl
lemma f42 : (2:Axis) = ⟨2,by decide⟩:= rfl
lemma f43 : (3:Axis) = ⟨3,by decide⟩:= rfl
lemma sign_neg (i j k:T): η i j k=- η i k j:= by fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [η,ℓ,loop, ← Fin.val_inj]
lemma spire (i j k:T): η i j k=η j k i:= by fin_cases i <;> fin_cases j <;> fin_cases k <;> unfold η <;> norm_num [ℓ,loop, ← Fin.val_inj]
lemma layout (t:ℝ)(i:T)(a b:Axis) : form t i a b=-form t i b a:= by fin_cases i<;> fin_cases a<;> fin_cases b <;>norm_num [form]
lemma straight (t:ℝ)(i:T)(a:Axis): form t i a a=0:= by linarith only [layout t i a a]
lemma sum4 (f:Axis→V)[AddCommMonoid V]: (∑ i,f i) = f 0+f 1+f 2+f 3:= Fin.sum_univ_four .. -- binder order
lemma sum3 (f:T→V)[AddCommMonoid V]: (∑ i,f i)=f 0+f 1+f 2:= Fin.sum_univ_three ..
-- quaternion identity
lemma η_rot (i j k:T): η i j k * η i j k= if i=j∨j=k∨k=i then (0:ℝ) else 1:= by fin_cases i<;>fin_cases j<;>fin_cases k<;>norm_num [η,ℓ,loop, ← Fin.val_inj]
-- row contraction f_i = J^+/- F with ∆
def η_at(i j:T)(a b:Axis):=∑ k:T, η i j k * mn k a b
lemma η_at_flips(i j:T)(a b:Axis):η_at i j a b= - η_at i j b a:= by unfold η_at; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro _ _; rw [←mul_neg,show mn _ b a= - mn _ a b from layout .., neg_neg]
lemma η_at_self(i j:T)(a:Axis):η_at i j a a=0:= by unfold η_at;simp_rw [mn,straight,mul_zero,Finset.sum_const_zero]
-- m table matrix.P0 helicity QM. calculate efficiently
set_option maxRecDepth 8000 in
set_option maxHeartbeats 5000000 in
lemma mm (i j:Tet)(a b:Axis): (∑ x:Axis, mn i a x* mn j x b) = (if i=j∧a=b then -1 else 0)+η_at i j a b:= by fin_cases i<;> fin_cases j<;> fin_cases a<;> fin_cases b<;> simp only [η_at,η,mn,form, ℓ,loop,Fin.sum_univ_four, Fin.sum_univ_three,← Fin.val_inj,Fin.val_zero,Fin.val_one]<;> norm_num [η,mn,form,ℓ,loop]
end YM.PositionX.Chir
