import YM.Integration.WilsonOriginalObservedRoseBornChiralUnary

/-! The first derivative of the subtracted two-point function uses both
orders of the proper means from each of its two registered directions. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralProducts

def centered (joint:ℝ)(a b:ℕ→ℝ):ℝ:=joint-a 0*b 1-a 1*b 0

theorem fee {a b u v S T U V:ℝ}(s:‖a-u‖≤S)(t:‖b-v‖≤T)(hu:‖u‖≤U)(hv:‖v‖≤V):
    ‖a*b-u*v‖ ≤ S*(T+V)+U*T:=by
  have nb:‖b‖ ≤ T+V:=calc
    ‖b‖ = ‖(b-v)+v‖ :=by rw [sub_add_cancel]
    _ ≤ ‖b-v‖+‖v‖ :=norm_add_le _ _
    _ ≤ T+V :=add_le_add t hv
  rw [show a*b-u*v=(a-u)*b+u*(b-v) by ring]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  exact add_le_add (mul_le_mul s nb (norm_nonneg _) ((norm_nonneg _).trans s))
    (mul_le_mul hu t (norm_nonneg _) ((norm_nonneg _).trans hu))

theorem original (J J':ℝ)(a b u v:ℕ→ℝ)(S T U V:ℝ)
    (first:∀q≤1,‖a q-u q‖≤S ∧ ‖u q‖≤U)
    (second:∀q≤1,‖b q-v q‖≤T ∧ ‖v q‖≤V):
    let C:=centered J a b-centered J' u v
    C=(J-J')-((a 0-u 0)*b 1+u 0*(b 1-v 1))-((a 1-u 1)*b 0+u 1*(b 0-v 0)) ∧
    ‖C‖ ≤ ‖J-J'‖+2*(S*(T+V)+U*T):=by
  intro C
  have z:=fee (first 0 (by decide)).1 (second 1 le_rfl).1 (first 0 (by decide)).2 (second 1 le_rfl).2
  have o:=fee (first 1 le_rfl).1 (second 0 (by decide)).1 (first 1 le_rfl).2 (second 0 (by decide)).2
  refine ⟨by dsimp only [C,centered];ring,?_⟩
  have con:C=(J-J')-(a 0*b 1-u 0*v 1)-(a 1*b 0-u 1*v 0):=by dsimp only [C,centered];ring
  rw [con, two_mul,←add_assoc]
  exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl z)) o)

end YM.Integration.WilsonOriginalObservedRoseBornChiralProducts
end
