import YM.Integration.WilsonIndependentCollarMaterialIntensity

/-! The actual sparse direction consumes exactly its mounted row wage.
Keep both the original recorded cable length and the separate connected
decay on its own relative lift. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarMaterialWallet
open Finset Function Lattice RG Wilson Precision PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Earn Marker Multi WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel.Address
open WilsonOriginalCensusDatedMaterial WilsonOriginalMixedBlockRows WilsonCoeffUV.Wheel.Express
open scoped Classical BigOperators
variable {G:Gauge}{n N m q:ℕ}{k:Fin n→ℕ}{σ:ℝ}{side:Side}{P:Passport side (Fin n)}{I:Type}
  {R:Run G}{B:I→Binder P (Stock.census (Fin n))}(H:Material R N m q k σ B)
  (base:Fin n→ℝ)(z:I)
local notation "h" => WilsonIndependentCollarSlateIntensity.amount (words H z) (B z).center
local notation "len₀" => (B z).length
local notation "rel₀" => feeH (toe (B z).mode.val (H.pin z) (H.root z) (H.frill z)) (H.pin z) (B z).mode.val

def bill:ℝ:=(Real.exp (σ*(len₀))*(h))/Poly.toll base (B z).mode

theorem exact_bill (pos:∀v,0<base v):Real.exp (σ*(len₀))*(h)=Poly.toll base (B z).mode*bill H base z:=by
  have p:0<Poly.toll base (B z).mode:=Finset.prod_pos fun v _=>pos v
  dsimp [bill]
  rw [mul_comm (Poly.toll base (B z).mode),div_mul_cancel₀ _ (ne_of_gt p)]

theorem original:
    Real.exp (σ*(len₀))*(h) ≤ Real.exp (σ*(len₀)-(32*σ)*(rel₀))*WilsonIndependentCollarMaterialIntensity.price H z:=by
  have price:=WilsonIndependentCollarMaterialIntensity.original H z
  calc
    _=Real.exp (σ*(len₀)-(32*σ)*(rel₀))*(Real.exp ((32*σ)*(rel₀))*(h)):=by
      rw [←mul_assoc,←Real.exp_add,sub_add_cancel]
    _≤ _:=mul_le_mul_of_nonneg_left price (Real.exp_pos _).le

end YM.Integration.WilsonIndependentCollarMaterialWallet
end
