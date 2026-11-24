import YM.Integration.WilsonIndependentCutJoinPlate
import YM.Integration.WilsonIndependentTwoMomentGrant
import YM.WilsonCoeffUV.Root.UV.GaugeSupply
import YM.Price.Intent

/-! Fund the full marked input/joint-output cashier and the conventional bare notebook together. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentCutJoinGrant
open RG.Supply Lattice RG XSpace Precision Source WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Uniform RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum
open RegulatorIR.Profiles RegulatorIR.Calibration RegulatorIR.Taping
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit
open WilsonIndependentEvenPassport (power)
open scoped Classical BigOperators ENNReal NNReal
variable {G:Gauge}{H:Hol G}(R:Master H)(chart:ChartRatio G)(K:KernelChoices)
    (V:XSpace.Run)(e h k j:ℕ)(Y:Program K)(branches:∀ p:Patch,p.Branches K G)
    (p b u:ℕ)(γ:ℝ)(lo:0<γ)(hi:γ<1)

open WilsonIndependentPublicPlateGrant (floor)
theorem canonical (simple:G.Simple)(sheet:RG.Supply.Sheet G)(hc:5≤j)(margin:h+3≤j)(width:p≤u)(rate:0<b)
    (supplement:ℕ) :
    let R:=primes G
    let K:=sheet.kernel
    let Y:=Oracle.books K
    let demand:=max supplement (floor (G:=G) K j Y p b u γ lo hi)
    ∃ B:WilsonIndependentEvenPassport.Menu R (Bare.chart G) K V e h k j demand,
      WilsonIndependentCutJoinPlate.Approved R (Bare.chart G) K V e h k j demand B ∧
        ∀ col:G.ColorIndex, WilsonIndependentTwoMomentGrant.Accounts R (Bare.chart G) K V e h k j Y sheet.has p b u γ demand col (by omega) B :=by
  intro R K Y demand
  obtain ⟨B,price⟩:=WilsonIndependentCutJoinPlate.purchase R (Bare.chart G) K V e h k j demand
    simple (Bare.chart_ratio G) sheet.has margin hc
  exact ⟨B,price,fun c=>WilsonIndependentTwoMomentGrant.paid R (Bare.chart G) K V e h k j Y sheet.has p b u γ lo hi demand c
    B simple hc width rate (Nat.le_max_right ..)⟩

end YM.Integration.WilsonIndependentCutJoinGrant
