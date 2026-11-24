import YM.Integration.WilsonPositionThermometerReading

/-! A numerical error bound on the exact connected polynomial of the
physical position thermometer. Only its seven occupied parts are charged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerOscillation
open Finset XSpace.Rose
open WilsonPositionThermometerConnected
open scoped Classical

private theorem pair {a b c d : ℂ} (ha : ‖a‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    ‖a*b-c*d‖ ≤ ‖a-c‖+‖b-d‖ := by
  calc
    ‖a*b-c*d‖ = ‖a*(b-d)+(a-c)*d‖ := by congr 1;ring
    _ ≤ ‖a*(b-d)‖ + ‖(a-c)*d‖ := norm_add_le _ _
    _ ≤ 1*‖b-d‖+‖a-c‖*1 := by
      rw [norm_mul,norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
    _ = _ := by ring

theorem difference {A B : Badge → ℂ} {δ : ℝ}
    (smallA : ∀ s : Badge,s.Nonempty → ‖A s‖ ≤ 1)
    (smallB : ∀ s : Badge,s.Nonempty → ‖B s‖ ≤ 1)
    (charged : ∀ s : Badge,s.Nonempty → ‖A s-B s‖ ≤ δ) :
    ‖value A-value B‖ ≤ 13*δ := by
  let v (s t : Badge) := A s*A t-B s*B t
  have two (s t : Badge) (hs : s.Nonempty) (ht : t.Nonempty) : ‖v s t‖ ≤ δ+δ :=
    (pair (smallA s hs) (smallB t ht)).trans (add_le_add (charged s hs) (charged t ht))
  let u := A univ-B univ
  let v₁ := v {0,1} {2}
  let v₂ := v {0,2} {1}
  let v₃ := v {1,2} {0}
  let w := A {0}*A {1}*A {2}-B {0}*B {1}*B {2}
  have h0 : ‖u‖ ≤ δ := charged _ (by decide)
  have h1 : ‖v₁‖ ≤ δ+δ := two _ _ (by decide) (by decide)
  have h2 : ‖v₂‖ ≤ δ+δ := two _ _ (by decide) (by decide)
  have h3 : ‖v₃‖ ≤ δ+δ := two _ _ (by decide) (by decide)
  have twoA : ‖A {0}*A {1}‖ ≤ 1 := by
    rw [norm_mul];calc _ ≤ 1*1 := mul_le_mul (smallA _ (by decide)) (smallA _ (by decide)) (norm_nonneg _) zero_le_one
                       _ = _ := one_mul _
  have h4 : ‖w‖ ≤ (δ+δ)+δ :=
    (pair twoA (smallB _ (by decide))).trans (add_le_add (two {0} {1} (by decide) (by decide)) (charged _ (by decide)))
  have heq : value A-value B = u-v₁-v₂-v₃+2*w := by dsimp only [value,u,v₁,v₂,v₃,v,w];ring
  rw [heq]
  have e1:=norm_sub_le u v₁
  have e2:=norm_sub_le (u-v₁) v₂
  have e3:=norm_sub_le (u-v₁-v₂) v₃
  have e4:=norm_add_le (u-v₁-v₂-v₃) (2*w)
  rw [norm_mul,show ‖(2:ℂ)‖=(2:ℝ) by norm_num] at e4
  linarith only [h0,h1,h2,h3,h4,e1,e2,e3,e4]

end YM.Integration.WilsonPositionThermometerOscillation
