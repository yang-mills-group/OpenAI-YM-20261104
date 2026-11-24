import YM.Integration.WilsonCoherentJointReturn

/-! Spend an original compact-source forecast on a different legitimately
funded chart. Physical orbital choices are made after the forecast. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentClockDebit
open Lattice Wilson RG Tree Precision
open RGComparison.Core16 RGComparison.Core16.Lumen FVA2 FVA2.CityHistory
open PertExtension.Series.Tested RGComparison.Core16.Lumen.Stage RGComparison.Core16.Therm
variable {G : Gauge} {c f : Side} {I : Type} [Fintype I] (J : I → Spool.Lamp G)
  (S : StepData c f) {P : Parcel.Oven S.patch} (X : P.Form G) {Z₀ Z : ChartRatio G}
  (front : LocalRatio Z₀) (back : LocalRatio Z) (large : Bid.Larger (G:=G) S)
  (T T' : Forest S.ratio) (u : Pins G c) (o : I → Site f)
  (paid : P.Offers X S.kernel) (inside : ∀a,‖u a‖≤X.Q)
  {U : Lumen.Stage} {r : ℕ} {C : ℝ}
  (money : Spool.Price U r C (Spool.rank J S T X Z₀ u o) (Spool.reads J S u o))
  (b : S.Choices) (v : (Descent.nil (top:=f)).Tags)

include front back paid inside money

theorem transferred :
    Spool.Price U r C (WilsonCoherentJointReturn.series J S T' Z u o large b v) (Spool.reads J S u o) := by
  rw [← WilsonCoherentJointReturn.same J S T' Z u o large b v X back paid inside]
  rw [← Spool.standard J o large inside T T' paid paid inside front back]
  exact money

theorem measured {g : ℝ} (positive : 0<g) (admitted : g≤Forge.dollar U.L) :
    ‖Spool.reads J S u o g - peval (WilsonCoherentJointReturn.series J S T' Z u o large b v) r g‖
      ≤ g^(r+1)*C :=
  (transferred J S X front back large T T' u o paid inside money b v).cost g positive admitted

end YM.Integration.WilsonCoherentClockDebit
end
