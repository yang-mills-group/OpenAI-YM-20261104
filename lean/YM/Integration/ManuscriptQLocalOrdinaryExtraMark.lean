import YM.Integration.ManuscriptQLocalOrdinaryDerivative
import YM.Comparison.RG02.Order.Pay

/-! The marked insertion on an original measured law uses one real additional
registry slot, even when every previous observable already has partners. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalOrdinaryExtraMark

open Finset Marker Multi Extra.Trajectories Comparison.RG02
open Primitives.GCC.Anchor
open scoped BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] (Γ : Census V)

def full : Order.Index 1 := ⟨Finset.univ,Finset.mem_univ _⟩
def lift (a : Poly Γ) := Order.Join.injectLeft Γ (Order.indices 1) a
def letter (a : Poly Γ) : Order.Grade Γ 1 :=
  Order.stamp Γ 1 (Polynomial.monomial 1 a)

def input (a b : Poly Γ) : Order.Grade Γ 1 := lift Γ a + letter Γ b

theorem plane (a : Poly Γ) (s : Γ.Mode) (q : Order.Index 1) :
    (letter Γ a).part (Order.Join.pair s q)=if q.val.card=1 then a.part s else 0 := by
  simpa [letter] using Order.split_monomial Γ 1 a 1 s q

theorem quiet (a : Poly Γ) : (letter Γ a).part (Order.Board Γ 1).quiet=0 := by
  rw [←Order.Join.pair_quiet,plane]
  simp [Census.quiet]

theorem base (a : Poly Γ) : (lift Γ a).part (Order.Board Γ 1).quiet=a.part Γ.quiet := by
  rw [←Order.Join.pair_quiet]
  rw [lift, Order.Join.left_part, if_pos rfl]

theorem hot (a b : Poly Γ) (s : Γ.Mode) :
    (input Γ a b).part (Order.Join.pair s full)=b.part s := by
  rw [input,Poly.part_plus,plane]
  simp [full,lift,Order.Join.left_part,Census.quiet,Subtype.ext_iff]

theorem cold (a b : Poly Γ) (s : Γ.Mode) :
    (input Γ a b).part (Order.Join.pair s (Order.indices 1).quiet)=a.part s := by
  rw [input,Poly.part_plus,plane]
  simp [lift,Order.Join.left_part,Census.quiet]

theorem twice (a : Poly Γ) : (letter Γ a)^2=0 := by
  unfold letter
  rw [←map_pow]
  ext z
  obtain ⟨⟨s,q⟩,rfl⟩:=(Order.Join.pairs Γ (Order.indices 1)).surjective z
  have bound : q.val.card≤1:=by simpa using q.val.card_le_univ
  change ((Order.stamp Γ 1) ((Polynomial.monomial 1 a)^2)).part (Order.Join.pair s q) = Poly.part 0 (Order.Join.pair s q)
  rw [pow_two,Polynomial.monomial_mul_monomial,Order.split_monomial]
  simp [show q.val.card≠1+1 by omega]

theorem product (a b : Poly Γ) : lift Γ a * letter Γ b = letter Γ (a*b) := by
  rw [letter,Order.stamp_monomial,letter,Order.stamp_monomial,lift,map_mul]
  ring

theorem single (b : Poly Γ) : connected (1+letter Γ b)=letter Γ b := by
  have h : (1+letter Γ b).part (Order.Board Γ 1).quiet=1 := by
    rw [Poly.part_plus,quiet]
    simp
  rw [Cumulants.log_formula h,Cumulants.unipotentLog]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro n _ hn
    have hs : 2≤n+1:=by omega
    rw [show 1-(1+letter Γ b) = -letter Γ b by abel,
      show n+1=2+(n+1-2) by omega,pow_add,neg_sq,twice,zero_mul,smul_zero]
  · simp

/-- The extra connected entry is measured on exactly the old normalized
law with all its modes, and then divided by that same full marked table. -/
theorem connected_full (a b : Poly Γ) (ha : a.part Γ.quiet=1) (s : Γ.Mode) :
    (connected (input Γ a b)).part (Order.Join.pair s full) =
      (b*inverseMass a).part s := by
  let c:=b*inverseMass a
  have hc : a*c=b := by
    dsimp [c]
    rw [mul_left_comm, right_inverse ha,mul_one]
  have hf : input Γ a b=lift Γ a*(1+letter Γ c) := by
    rw [mul_add,mul_one,product,hc]
    rfl
  have hl : (lift Γ a).part (Order.Board Γ 1).quiet=1 := (base Γ a).trans ha
  have h₁ : (1+letter Γ c).part (Order.Board Γ 1).quiet=1 := by
    rw [Poly.part_plus,quiet]
    simp
  have hg:=Cumulants.log_map (Order.Join.injectLeft Γ (Order.indices 1))
    (base Γ) ha
  change lift Γ (connected a) = connected (lift Γ a) at hg
  rw [hf,Cumulants.connected_mul hl h₁,single,←hg]
  exact hot Γ (connected a) c s

theorem material (a : Poly Γ) (u : ℂ) :
    input Γ a (u • a)=lift Γ a*(1+letter Γ (u • (1:Poly Γ))) := by
  rw [mul_add,mul_one,product,mul_smul_comm,mul_one]
  rfl

end YM.Integration.ManuscriptQLocalOrdinaryExtraMark
end
