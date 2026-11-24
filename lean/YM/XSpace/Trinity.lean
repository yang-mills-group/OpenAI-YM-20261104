import YM.XSpace.Pub
/-!
# Orientation conventions for triangle test

Initially use sqrt2 times normalized e to keep integer tables on lines. Keep account of this in label normalizations.
`PlaqAxes` are `Axis` unordered-positive with increasing indices. orientation `(0,1,2,3)` positive.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chiral
open Function Set Filter Lattice
open scoped BigOperators Topology
abbrev P := Fin 3
private def ki (a b : Axis) : ℤ:= if a=b then 1 else 0
private def kuI (a b : P):ℤ:= if a=b then 1 else 0
private def lead (a b:P) : ℤ:= if a+1=b then 1 else 0
private def eps (a b c:P):ℤ:= lead a b* lead b c - lead b a * lead a c -- check neg orientation? negative order b=a-1,c=a+1 second term lead b a & lead a c yes. first c=b+1.
private def signI (σ:Bool):ℤ:=if σ then 1 else -1
def shard (a:P): Axis := a.succ
def strong (a:P): PlaqAxes:=⟨(0,shard a),Fin.pos_iff_ne_zero.mpr (Fin.succ_ne_zero a)⟩
def triCoeff (σ:Bool)(p:P)(a b:Axis):ℤ:= ki a 0 * ki b (shard p) - ki a (shard p) * ki b 0 + signI σ *(ki a (shard (p+1))*ki b (shard (p+2))-ki a (shard (p+2))*ki b (shard (p+1)))
-- Bool true is PLUS. nil otherwise. anti on both slots
abbrev q (σ:Bool)(p:P) : Axis→Axis→ℝ:= fun a b=> triCoeff σ p a b
def liftedSign (a b c:P):ℝ:=eps a b c
def sig (σ:Bool):ℝ:=signI σ
abbrev six (φ:PlaqAxes) := φ.val.1
abbrev endr (φ:PlaqAxes) := φ.val.2
private def without (a b c d:Axis):ℤ:= ki a c*ki b d-ki a d * ki b c
private def levi4 (a b c d:Axis):ℤ:= (∑ i:P,triCoeff true i a b*triCoeff true i c d)-without a b c d
def Ω (a b c d:Axis):ℝ:=levi4 a b c d

private theorem test1 : ∀ b:Bool,∀ i:P,∀ j k:Axis, triCoeff b i j k= -triCoeff b i k j:= by decide
private theorem test2 : ∀ i j k:P, eps i i k=0∧eps i j k= -eps i k j ∧ eps i j k=eps j k i:=by decide
@[simp] lemma lift0 (i j:P):liftedSign i i j=0:=by simp [liftedSign, (test2 i i j).1]
lemma lift_swap (i j k:P): liftedSign i k j= -liftedSign i j k:=by unfold liftedSign; exact_mod_cast (test2 i k j).2.1
lemma revolves (i j k:P): liftedSign i j k=liftedSign j k i:=by unfold liftedSign; exact_mod_cast (test2 i j k).2.2
lemma chosen_sqrt2 (σ:Bool)(i:P)(a b:Axis): q σ i b a= -q σ i a b:= by unfold q; exact_mod_cast test1 σ i b a
lemma qdiag (σ:Bool)(i:P)(a:Axis) : q σ i a a=0:=by have h:=chosen_sqrt2 σ i a a; linarith
@[simp] lemma sign_pos : sig true=1 :=Int.cast_one
@[simp] lemma sign_neg : sig false= -1 := by unfold sig signI; norm_num
set_option maxRecDepth 8000 in
private theorem test3 : ∀ (σ τ:Bool)(i j:P), (∑ p:PlaqAxes,triCoeff σ i (six p) (endr p)*triCoeff τ j (six p) (endr p))= if σ=τ∧ i=j then 2 else 0 := by decide
lemma ortho (σ τ:Bool)(i j:P): (∑ p:PlaqAxes,q σ i (six p) (endr p)*q τ j (six p) (endr p))= if σ=τ∧ i=j then 2 else 0:=by
  unfold q; split_ifs with h; exact_mod_cast Eq.trans (test3 σ τ i j) (if_pos h); exact_mod_cast Eq.trans (test3 σ τ i j) (if_neg h)
private theorem test4 : ∀ (σ:Bool)(i j:P)(a b:Axis), (∑ m:Axis,triCoeff σ i a m * triCoeff σ j m b)= - kuI i j * ki a b - signI σ * ∑ k:P, eps i j k * triCoeff σ k a b:= by decide
abbrev dotI (a b: Axis):ℝ:=ki a b
def dot3 (i j:P):ℝ:=kuI i j
lemma dot_at (a b:Axis) : dotI a b= if a=b then 1 else 0:=by unfold dotI ki; split_ifs <;> simp
lemma dotC (a b:P) : dot3 a b= if a=b then 1 else 0:=by unfold dot3 kuI; split_ifs <;> simp
lemma spec_algebra (σ:Bool)(p r:P) (i j:Axis): (∑ k:Axis, q σ p i k * q σ r k j)= -dot3 p r * dotI i j-sig σ*∑ x:P,liftedSign p r x * q σ x i j:= by unfold q dot3 dotI sig liftedSign; exact_mod_cast test4 σ p r i j
set_option maxRecDepth 8000 in
private theorem test5 : ∀ i t j:P,∀ a b:Axis, (∑ m:Axis,∑ n:Axis,triCoeff false i a m*triCoeff false t m n*triCoeff false j b n)+(∑ m:Axis,∑ n:Axis,triCoeff false i b m*triCoeff false t m n*triCoeff false j a n)=2*eps i t j*ki a b:=by decide
lemma convolve (i t j:P)(a b:Axis): (∑ m:Axis,∑ n:Axis,q false i a m*q false t m n*q false j b n)+(∑ m:Axis,∑ n:Axis,q false i b m*q false t m n*q false j a n)=2*liftedSign i t j*dotI a b:=by unfold q liftedSign dotI; exact_mod_cast test5 i t j a b
private theorem test6 : ∀ (σ:Bool)(a b c d:Axis), (∑ i:P,triCoeff σ i a b * triCoeff σ i c d)= without a b c d + signI σ * levi4 a b c d:= by decide
lemma split4 (σ:Bool)(a b c d:Axis): (∑ i:P,q σ i a b*q σ i c d)= dotI a c*dotI b d-dotI a d*dotI b c+ sig σ*Ω a b c d:=by unfold q dotI sig Ω; have h:=test6 σ a b c d; unfold without at h; exact_mod_cast h
private theorem test7 : ∀ a b c d : Axis, levi4 a b c d= -levi4 b a c d ∧ levi4 a b c d= -levi4 a b d c ∧ levi4 a b c d= -levi4 a c b d :=by decide
lemma e₁ (a b c d:Axis): Ω a b c d= -Ω b a c d:=by unfold Ω; exact_mod_cast (test7 a b c d).1
lemma e₂ (a b c d:Axis): Ω a b c d= -Ω a c b d:=by unfold Ω; exact_mod_cast (test7 a b c d).2.2
lemma e₃ (a b c d:Axis): Ω a b c d= -Ω a b d c:=by unfold Ω; exact_mod_cast (test7 a b c d).2.1
lemma e_pos : Ω 0 1 2 3 = 1:= by unfold Ω; exact_mod_cast (show levi4 0 1 2 3=1 by decide)
private theorem test8 : ∀ (σ:Bool)(a b:Axis)(i:P), (∑ c:Axis,∑ d:Axis, levi4 a b c d*triCoeff σ i c d)= 2*signI σ*triCoeff σ i a b:=by decide
lemma chirality (σ:Bool)(i:P)(a b:Axis): (∑ c:Axis,∑ d:Axis,Ω a b c d*q σ i c d)=2*sig σ*q σ i a b:=by unfold Ω q sig; exact_mod_cast test8 σ a b i
-- normalized directions in the actual diagnostic

def qNorm (σ:Bool)(i:P)(a b:Axis):= (Real.sqrt 2)⁻¹ * q σ i a b
lemma physical_axes (σ τ:Bool)(i j:P) : (∑ p:PlaqAxes,qNorm σ i (six p) (endr p)*qNorm τ j (six p) (endr p))= if σ=τ ∧ i=j then 1 else 0:=by
  unfold qNorm; simp_rw [mul_mul_mul_comm ((Real.sqrt 2)⁻¹) _ (Real.sqrt 2)⁻¹, ← Finset.mul_sum,ortho]; split_ifs <;> norm_num; rw [← pow_two, inv_pow, Real.sq_sqrt (by norm_num),inv_mul_cancel₀ (by norm_num)]
end YM.XSpace.Chiral
