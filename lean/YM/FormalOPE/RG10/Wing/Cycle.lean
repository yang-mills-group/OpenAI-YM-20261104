import YM.FormalOPE.RG10.GaugeGear.Home
/-! # Formal Ward flow in cutoff-rank controlled polynomial packet. Iterates & product calculus
 with exact factorial convention. Use *separate time parameter*, no physical extent.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Wing.Cycle
open Function Finset PowerSeries
open scoped Topology BigOperators Classical
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D:Derivation ℂ A A)
variable (p q : A)
variable {i j k :ℕ}
def powers (t:ℕ) : A →ₗ[ℂ] A := D.toLinearMap ^ t
def numeral (k: ℕ) :A→ₗ[ℂ] A:= ((↑k.factorial:ℂ)⁻¹) • powers D k
local notation "u"=> powers D
local notation "v"=> numeral D
lemma steady : u 0 p=p:= rfl
lemma newDay : u (i+1) p=D (u i p):= by unfold powers; rw [pow_succ']; rfl
lemma oldDay : u (i+1) p=u i (D p):= by unfold powers; rw [pow_succ]; rfl
@[simp] lemma precise_zero : v 0 p=p:= by simp [numeral,steady]
lemma thick : D (v i p) = ((i:ℂ)+1) • v (i+1) p:= by
 unfold numeral; simp only [Nat.factorial_succ, LinearMap.smul_apply, Derivation.map_smul,newDay,Nat.cast_mul,Nat.cast_add,Nat.cast_one,smul_smul]; have hh : (i:ℂ)+1 ≠ 0:= by exact_mod_cast Nat.succ_ne_zero i
 congr 1; field_simp [i.factorial_ne_zero]
lemma thick_stamp : v (i+1) p= ((i:ℂ)+1)⁻¹ • D (v i p) := by rw [thick, inv_smul_smul₀ (show (i:ℂ)+1 ≠ 0 by exact_mod_cast Nat.succ_ne_zero i)]
lemma alive : v i p=0 ↔ u i p=0 := by unfold numeral; rw [LinearMap.smul_apply, smul_eq_zero]; simp [i.factorial_ne_zero]
lemma busy (h:v i p=0) (he:i≤j): v j p=0:= by
 induction j,he using Nat.le_induction with
 | base=> exact h
 | succ j he ih=>rw [thick_stamp,ih,map_zero,smul_zero]
-- normalized Pascal Leibniz
lemma pascal : v k (p*q)= ∑ i∈ antidiagonal k, v i.1 p * v i.2 q:= by
 induction k with
 | zero=>simp --
 | succ k ih=>
    -- multiply lhs by k+1 then Antidiagonal.Sm sums with k+1 restored
    rw [← smul_right_inj (R:=ℂ) (r:=(k:ℂ)+1) (by exact_mod_cast Nat.succ_ne_zero k),← thick, ih,map_sum]
    let X := fun (x:ℕ×ℕ) => v x.1 p * v x.2 q
    let f (x:ℕ×ℕ):= (↑x.1:ℂ) • X x
    let g (x:ℕ×ℕ):= (↑x.2:ℂ) • X x
    have hx (x:ℕ×ℕ): D (X x)= f (x.1+1,x.2)+g (x.1,x.2+1):= by unfold X; rw [Derivation.leibniz,thick,thick, add_comm]; unfold f g X; push_cast; rw [smul_eq_mul,_root_.mul_comm (v x.2 q),smul_mul_assoc,smul_eq_mul,mul_smul_comm]
    have hl : (↑k+1:ℂ) • ∑ i∈ antidiagonal (k+1), X i = ∑ i∈antidiagonal (k+1), f i + ∑ i∈antidiagonal (k+1), g i := by
       rw [← sum_add_distrib, smul_sum]; apply sum_congr rfl; intro x hx; unfold f g; rw [← add_smul]; congr 1; exact_mod_cast (mem_antidiagonal.mp hx).symm -- unfold f g
    rw [hl]; change ∑ i∈antidiagonal k,D (X i)= _; simp_rw [hx,sum_add_distrib, Finset.Nat.sum_antidiagonal_succ (f:=f), Finset.Nat.sum_antidiagonal_succ' (f:=g)];
    -- inspect
    simp [f,g,X]
lemma void (a b t:ℕ)(hh:v (a+1) p=0)(hj:v (b+1) q=0)(ht:a+b<t) : v t (p*q)=0:= by
 rw [pascal]; apply sum_eq_zero; intro i hi; by_cases hx: a+1 ≤ i.1
 · rw [busy D p hh hx,zero_mul]
 rw [busy D q hj (show b+1 ≤ i.2 by have he:= mem_antidiagonal.mp hi; omega),mul_zero]
end YM.FormalOPE.RG10.Wing.Cycle
