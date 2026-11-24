import YM.Integration.WilsonPositionScaleLawThermometerChart

/-! A pointwise price for the original signed connected triple from seven
ordinary, unconnected entries, retaining the two single-product contributions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerError
open Finset XSpace XSpace.Rose WilsonPositionThermometerConnected
open scoped Classical

private theorem pair (a b c d:ℂ):‖a*c-b*d‖≤‖a‖*‖c-d‖+‖a-b‖*‖d‖:=by
  rw [show a*c-b*d=a*(c-d)+(a-b)*d by ring]
  simpa only [norm_mul] using norm_add_le (a*(c-d)) ((a-b)*d)

private theorem sums (a b c d e:ℂ):‖a-(b+c+d)+2*e‖≤‖a‖+(‖b‖+‖c‖+‖d‖)+2*‖e‖:=by
  have twice:‖(2:ℂ)*e‖=2*‖e‖:=by rw [norm_mul];norm_num
  linarith [norm_add_le (a-(b+c+d)) (2*e),norm_sub_le a (b+c+d),norm_add_le (b+c) d,norm_add_le b c]

theorem price (A B:Badge→ℂ){R e:ℝ}(hR:0≤R)(he:0≤e)
    (left:∀s:Badge,s.Nonempty→‖A s‖≤R)(right:∀s:Badge,s.Nonempty→‖B s‖≤R)
    (fee:∀s:Badge,s.Nonempty→‖A s-B s‖≤e):
    ‖value A-value B‖≤(1+6*R+6*R^2)*e:=by
  let d (s t:Badge):=A s*A t-B s*B t
  have two (s t:Badge)(hs:s.Nonempty)(ht:t.Nonempty):‖d s t‖≤2*R*e:=by
    calc _≤‖A s‖*‖A t-B t‖+‖A s-B s‖*‖B t‖:=pair ..
         _≤R*e+e*R:=add_le_add (mul_le_mul (left s hs) (fee t ht) (norm_nonneg _) hR)
            (mul_le_mul (fee s hs) (right t ht) (norm_nonneg _) he)
         _=2*R*e:=by ring
  let z:=A {0}*A {1}*A {2}-B {0}*B {1}*B {2}
  have three:‖z‖≤3*R^2*e:=by
    calc _≤‖A {0}*A {1}‖*‖A {2}-B {2}‖+‖d {0} {1}‖*‖B {2}‖:=pair ..
         _≤(R*R)*e+(2*R*e)*R:=by
            rw [norm_mul]
            exact add_le_add (mul_le_mul (mul_le_mul (left _ (by decide)) (left _ (by decide)) (norm_nonneg _) hR)
              (fee _ (by decide)) (norm_nonneg _) (mul_nonneg hR hR))
              (mul_le_mul (two _ _ (by decide) (by decide)) (right _ (by decide)) (norm_nonneg _) (by positivity))
         _=3*R^2*e:=by ring
  have exactValue:value A-value B=(A univ-B univ)-(d {0,1} {2}+d {0,2} {1}+d {1,2} {0})+2*z:=by
    dsimp [value,d,z];ring
  rw [exactValue]
  calc _≤‖A univ-B univ‖+(‖d {0,1} {2}‖+‖d {0,2} {1}‖+‖d {1,2} {0}‖)+2*‖z‖:=sums ..
       _≤e+(2*R*e+2*R*e+2*R*e)+2*(3*R^2*e):=by
          exact add_le_add (add_le_add (fee _ (by decide))
            (add_le_add (add_le_add (two _ _ (by decide) (by decide)) (two _ _ (by decide) (by decide)))
              (two _ _ (by decide) (by decide)))) (mul_le_mul_of_nonneg_left three (by norm_num))
       _=(1+6*R+6*R^2)*e:=by ring

end YM.Integration.WilsonPositionScaleLawThermometerError
end
