import YM.Integration.WilsonMeasuredPublicEntrancePositiveRay

/-! A separate nonnegative leading scalar is allowed on each recorded field. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace YM.Integration.WilsonMeasuredPublicEntrancePositiveFlag
open Module Finset
variable {E I:Type*} [AddCommGroup E] [Module ℂ E] [Fintype I]

def below (w:I→ℕ×ℕ)(i j:I):Prop:=
  (w i).1<(w j).1 ∨ (w i).1=(w j).1 ∧ (w i).2<(w j).2

theorem original (B:Basis I ℂ E)(w:I→ℕ×ℕ)(T:Module.End ℂ E)
    (mass:E→ℝ)(pd:∀v:E,v≠0→0 < mass v)
    (para:∀u v,mass (u+v)+mass (u-v)=2*(mass u+mass v))
    (square:∀(s:ℝ)(v:E),mass ((s:ℂ)•v)=s^2*mass v)(iso:∀v,mass (T v)=mass v)
    (price:I→ℝ)(nonneg:∀j,0 ≤ price j)
    (filed:∀i j,¬below w i j→B.coord i (T (B j)-(price j:ℂ)•B j)=0):T=1:=by
  have scan (a b:ℕ):∀j,(w j).1=a→(w j).2=b→T (B j)=B j:=by
    induction a using Nat.strong_induction_on generalizing b with
    | h a grade =>
      induction b using Nat.strong_induction_on with
      | h b leg =>
        intro j ha hb
        let v:=T (B j)-(price j:ℂ)•B j
        have fixed:T v=v:=by
          obtain repr:=B.sum_repr v
          rw [←repr,map_sum]
          apply Finset.sum_congr rfl
          intro i _
          by_cases prior:below w i j
          · have old:T (B i)=B i:=by
              obtain lower|⟨own,low⟩:=prior
              · exact grade (w i).1 (ha ▸ lower) (w i).2 i rfl rfl
              exact leg (w i).2 (hb ▸ low) i (own.trans ha) rfl
            rw [map_smul,old]
          · have zero:B.repr v i=0:=filed i j prior
            rw [zero,zero_smul,map_zero]
        exact WilsonMeasuredPublicEntrancePositiveRay.fixed T v (B j) fixed
          mass pd para square iso (nonneg j) (k:=1) (by dsimp only [v];rw [one_smul];abel)
  exact B.ext (fun j=>scan (w j).1 (w j).2 j rfl rfl)
end YM.Integration.WilsonMeasuredPublicEntrancePositiveFlag
