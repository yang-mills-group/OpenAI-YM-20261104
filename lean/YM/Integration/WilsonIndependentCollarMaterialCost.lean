import YM.Integration.WilsonIndependentCollarMaterialWallet

/-! Finite angular and coupling multiplicity of the actual dated rooted bank.
The physical dose and fixed engineering power are outside this multiplicity. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarMaterialCost
open Finset Function Lattice RG Wilson Precision QuadraticLocal QuadraticLocal.Earn Marker Multi Push Push.PriceCompiler
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Express WilsonOlderFreshConnectedRobe WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedBirth WilsonOriginalCensusDatedMaterial WilsonRegisteredPairUnaryWallet
open WilsonOlderFreshGraphPointWallet (point)
open PhysicalNext.Repeat.Legato Push.AbsoluteSums Push.Local
open scoped Classical BigOperators
variable {G:Gauge}{n N m q:ℕ}{k:Fin n→ℕ}{σ:ℝ}{side:Side}{P:Passport side (Fin n)}{I:Type}
  {R:Run G}{B:I→Binder P (Stock.census (Fin n))}(H:Material R N m q k σ B)(z:I)
open WilsonIndependentCollarMaterialIntensity (price)
local notation "s" => (B z).mode.val

theorem original : price H z ≤ ((q+1:ℕ):ℝ)*((mass k s+q+1:ℕ):ℝ)*
    ((∏v∈s,‖H.source z v‖)*|(R.family.path.levels.clock.hatBeta m)^H.allowance*
      H.amplitude^(s).card|) := by
  classical
  let M:ℝ:=(R.family.path.levels.clock.hatBeta m)^H.allowance*H.amplitude^(s).card
  have hp:0≤∏v∈s,‖H.source z v‖:=Finset.prod_nonneg fun _ _=>norm_nonneg _
  apply le_trans (b:=∑ _l : Fin (q+1), ((mass k s+q+1:ℕ):ℝ)*((∏v∈s,‖H.source z v‖)*|M|))
  · unfold price
    apply Finset.sum_le_sum
    intro l _
    change ((mass k s+l.val+1:ℕ):ℝ)*((∏v∈s,‖H.source z v‖)*M) ≤ _
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self M) hp)
      (Nat.cast_nonneg _)) ?_
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by have:=l.isLt; omega)) (mul_nonneg hp (abs_nonneg M))
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,M]
    rw [←mul_assoc]

end YM.Integration.WilsonIndependentCollarMaterialCost
end
