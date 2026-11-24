import YM.FormalBulk08.Orb.Topaz
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Field tensor convention (`C/r!` repeated derivatives), unstructured real slots. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lava
open Series Wick Orb Function
open MvPolynomial
open scoped BigOperators Classical
variable {V : Type*}
abbrev chain (V : Type*) (r : ℕ) := Fin r → V
abbrev Tile (V : Type*) (r : ℕ) := chain V r → ℝ
def Agate {r : ℕ} (T : Tile V r) := ∀ (v : chain V r) (s : Equiv.Perm (Fin r)), T (v ∘ s)=T v
lemma Agate.add {r : ℕ} {T S : Tile V r} (a : Agate T) (b : Agate S) : Agate (T+S) := by intro v s; rw [Pi.add_apply, Pi.add_apply,a,b]
lemma Agate.sub {r : ℕ} {T S : Tile V r} (a : Agate T) (b : Agate S) : Agate (T-S) := by intro v s; rw [Pi.sub_apply,Pi.sub_apply,a,b]
lemma Agate.smul {r : ℕ} {T : Tile V r} (a : Agate T) (c : ℝ) : Agate (c • T) := by intro v s; rw [Pi.smul_apply,Pi.smul_apply,a]
lemma agate_zero (r : ℕ) : Agate (0 : Tile V r) := by intro v s; rfl
lemma Agate.sums {r : ℕ} {J : Type*} (B : Finset J) {T : J → Tile V r} (a : ∀ i∈B, Agate (T i)) : Agate (∑ i∈B, T i) := by
   intro v s; simp_rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i hi=>a i hi v s

def sand {r : ℕ} (T : Tile V r) : Tile V r := fun v => (∑ s : Equiv.Perm (Fin r), T (v ∘ s)) / Fintype.card (Equiv.Perm (Fin r))
lemma agate_sand {r : ℕ} (T : Tile V r) : Agate (sand T) := by
   intro v s; unfold sand; congr 1; refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ (fun i=> ?_); rfl
lemma sand_fixed {r : ℕ} {T : Tile V r} (a : Agate T) : sand T=T := by
   unfold Agate at a; funext i; unfold sand; simp_rw [a]; simp

def cards {r : ℕ} (v : chain V r) : TypeR V := ∏ i,X (v i)
lemma cards_agate {r : ℕ} (v : chain V r) (s : Equiv.Perm (Fin r)) : cards (v ∘ s)=cards v := Fintype.prod_equiv s _ _ fun _=> rfl
lemma cards_cons {r : ℕ} (a : V) (v : chain V r) : cards (Fin.cons a v : chain V (r+1))=X a * cards v := by simp [cards,Fin.prod_univ_succ]

variable [Fintype V] (r : ℕ)
def facade : Tile V r →ₗ[ℝ] TypeR V where
   toFun T:= ∑ v:chain V r, C (T v) * cards v
   map_add' A B:= by simp [add_mul, Finset.sum_add_distrib]
   map_smul' a b:= by simp [Finset.smul_sum,smul_eq_C_mul,mul_assoc]
lemma facade_eq (T : Tile V r) : facade r T=∑ v,C (T v)*cards v := rfl
lemma facade_grade (T : Tile V r) : IsHomogeneous (facade r T) r := by
   rw [facade_eq]; refine IsHomogeneous.sum _ _ _ fun i _ => IsHomogeneous.C_mul ?_ _
   have h := IsHomogeneous.prod Finset.univ (fun j:Fin r => X (i j) : Fin r → TypeR V) (fun _=>1) (fun j _=> isHomogeneous_X _ (i j)) -- parse
   simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,cards,mul_one,Nat.cast_id] using h
lemma sand_facade (T : Tile V r) : facade r (sand T)=facade r T := by
   simp_rw [facade_eq,sand,div_eq_mul_inv,Finset.sum_mul,_root_.map_sum,Finset.sum_mul];rw [Finset.sum_comm]
   let N := Fintype.card (Equiv.Perm (Fin r))
   have h (s : Equiv.Perm (Fin r)) : ∑ v:chain V r, C (T (v ∘ s) * (N:ℝ)⁻¹) * cards v= C (N:ℝ)⁻¹ * facade r T := by
      rw [facade_eq,Finset.mul_sum]; refine Fintype.sum_equiv (Equiv.arrowCongr s.symm (Equiv.refl V)) _ _ fun v=>?_ ;change C _ * _= C _ * (C (T (v ∘ s))*cards (v ∘ s)); rw [cards_agate,_root_.map_mul]; ring
   change (∑ s:Equiv.Perm (Fin r), ∑ v:chain V r,C (T (v ∘ s)*(N:ℝ)⁻¹)*cards v) = _; simp_rw [h]; rw [←facade_eq]; have hn : (N:ℝ)≠0 := by unfold N; positivity
   simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; rw [←mul_assoc]
   change (N: TypeR V)* _*_=_; rw [←_root_.map_natCast C,←_root_.map_mul,mul_inv_cancel₀ hn,map_one,one_mul]
end YM.FormalBulk08.Lava
