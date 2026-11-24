import YM.Integration.WilsonIndependentConditionalNativeVerse

/-! The native unmarked positive-rank output on the same conditional as the complete marked verse. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalNativeVacuum
open Lattice RG WilsonCoeffUV Laurent Bloch Metric WilsonCoeffUV.Blue
open FreeResolvent Work.F08 WilsonCoeffUV.Bank Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil Precision Embroider RegulatorIR RegulatorIR.Diagram
open RegulatorIR.Oracle RegulatorIR.Quadratic RegulatorIR.Step RegulatorIR.Prim RegulatorIR.Ledger
open RegulatorIR.Budget RegulatorIR.Budget.Packet
open WilsonIndependentConditionalUnshiftedExit WilsonIndependentConditionalCoordinateHeat
open WilsonIndependentConditionalNativeLinks
open scoped BigOperators Matrix Classical
variable {G:Gauge}{Ω:Type}{M:Ω→ℕ}{n:Page M→Side}
variable {A:Levels G}{C:Circuit M n}{K:KernelChoices}{s:ℕ}{w:Ω}
variable (R:WilsonIndependentPublicFreeTrain.Matches A C K s w)
variable (Y:Program K)(Z:∀P:Patch,P.Branches K G)(t:Page M→RegulatorIR.Binding.Scale)
variable (f:Flap M)(hw:f.volW=w)
local notation "N₀" => s+M w
local notation "m₀" => s+(M w-(f.offset+1))
local notation "P₀" => loose A m₀
local notation "D₀" => C.devices Y G Z t f
include R hw

theorem submitted {d:ℕ}(T:Orders (Foot G))(W:Orders (Cloth (Hinge G (P₀).L)))
    (prior:∀e≤d,∀ r,0<r→(D₀).jVac T e r=WilsonIndependentConditionalCoordinateHeat.row (joint G P₀) (W e r))
    {e r:ℕ}(he:e≤d)(hr:0<r):
    let Γ:=WilsonIndependentConditionalUnshiftedQuiet.kernel P₀ (shuttleM (conditional A N₀ m₀))
    let pred:=post P₀ (shuttleM (feedA A N₀ m₀))
    (D₀).pure T e r=WilsonIndependentConditionalCoordinateHeat.row (coarse G)
       (scoop (Packet.draft pred.transpose (ceaseHeat Γ W false e r))):=by
  intro Γ pred
  let q:=joint G P₀
  have paid(j:ℕ):logHeat (D₀).line ((D₀).jVac T) false j e=logHeat (D₀).line (orders q W) false j e:=
    WilsonIndependentConditionalThermalCap.quiet (D₀).line prior j e he
  have inc:ceaseHeat (D₀).line ((D₀).jVac T) false e=ceaseHeat (D₀).line (orders q W) false e:=by
    unfold ceaseHeat heated
    funext h;exact Finset.sum_congr rfl (fun j _=>congrFun (paid j) h)
  rw [GridStep.pure,if_neg (by omega),congrFun inc r,WilsonIndependentConditionalNativeLinks.covariance R Y Z t f hw]
  change (D₀).pullI (ceaseHeat (line q Γ) (orders q W) false e r)=_
  rw [WilsonIndependentConditionalCoordinateVerse.quiet]
  exact WilsonIndependentConditionalNativeLinks.pull R Y Z t f hw _

end YM.Integration.WilsonIndependentConditionalNativeVacuum
