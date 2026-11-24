import YM.Integration.WilsonIndependentTwoMomentPlate
import YM.Integration.WilsonIndependentPublicPlateGrant
import YM.WilsonCoeffUV.Root.UV.GaugeSupply
import YM.Price.Intent

/-! The public bare chart and canonical Wilson stencils on one shared-moment passport. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentTwoMomentGrant
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
variable (extra:ℕ)
def Accounts (col:G.ColorIndex)(hj:4≤j)(B:WilsonIndependentEvenPassport.Menu R chart K V e h k j extra) : Prop :=
      ∀ (z:Requests B.a→ℝ)(money:∀ i,0≤z i),
        let C:=S V B.a B.positive j hj
        let L:=WilsonIndependentGroupedOrbitBills.meter C z money
        let c:=C.leadA Y G (quantum b u)
        SatisfiesQ G Y C branches (stampE C z money) p (quantum b u) γ ∧
        ∃ F:Tent (M V B.a), Notebook C Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p ∧
          (∀ i:Requests B.a,sheet F (Page.opening _ i)=Clocks.flat) ∧
          let T:=C.lane Y G branches (sheet F)
          Cylinder T (C.payroll Y G branches (sheet F)) (C.pushP Y G) (C.takeP Y G) L c p b u ∧
            Lantern (C.dialect Y G branches (sheet F)) (RegulatorIR.FVAAlt2.Rocket.native _) L c γ ∧ T.Endings L

variable (col:G.ColorIndex)
theorem paid (B:WilsonIndependentEvenPassport.Menu R chart K V e h k j extra) (simple:G.Simple)(late:5≤j)(width:p≤u)
    (rate:0<b)(cap:floor (G:=G) K j Y p b u γ lo hi≤extra) :
    Accounts R chart K V e h k j Y branches p b u γ extra col (by omega) B := by
  intro z money C L c
  have grades (m:ℕ) (hm:m∈stages j) : 5≤m :=by simp [stages] at hm;omega
  have numeric (f:Flap (M V B.a)) := cap.trans (B.pre.trans (lengths V B.a j B.positive (by omega:4≤j) f))
  have grow : p+2≤quantum b u:=by dsimp [quantum];omega
  have minimum : 3≤quantum b u:=by dsimp [quantum];omega
  have pre:=WilsonIndependentGroupedShelves.original G Y branches C (stages j) p (quantum b u)
    γ lo hi grades grow minimum numeric (patches V B.a j B.positive (by omega))
    (page V B.a j B.positive (by omega)) (WilsonIndependentLicensedCircuit.patch V B.a j B.positive (by omega)) z money
  obtain ⟨F,notes,reference⟩:=WilsonIndependentLicensedCircuit.notebook V B.a j B.positive (by omega) K Y branches col p
  refine ⟨pre,F,notes,reference,?_⟩
  exact WilsonIndependentGroupedOrbitBills.original G Y branches C z money F col simple
    pre (fun i=>(units V B.a B.positive j (by omega) i).1) notes rate
    (V.finalSide.side.val*V.ratio^B.a) (ends V B.a B.positive)

theorem canonical (simple:G.Simple)(sheet:RG.Supply.Sheet G)(hc:5≤j)(margin:h+3≤j)(width:p≤u)(rate:0<b)
    (supplement:ℕ) :
    let R:=primes G
    let K:=sheet.kernel
    let Y:=Oracle.books K
    let demand:=max supplement (floor (G:=G) K j Y p b u γ lo hi)
    ∃ B:WilsonIndependentEvenPassport.Menu R (Bare.chart G) K V e h k j demand,
      WilsonIndependentTwoMomentPlate.Approved R (Bare.chart G) K V e h k j demand B ∧
        ∀ col:G.ColorIndex, Accounts R (Bare.chart G) K V e h k j Y sheet.has p b u γ demand col (by omega) B :=by
  intro R K Y demand
  obtain ⟨B,price⟩:=WilsonIndependentTwoMomentPlate.purchase R (Bare.chart G) K V e h k j demand
    simple (Bare.chart_ratio G) sheet.has margin hc
  exact ⟨B,price,fun c=>paid R (Bare.chart G) K V e h k j Y sheet.has p b u γ lo hi demand c
    B simple hc width rate (Nat.le_max_right ..)⟩

end YM.Integration.WilsonIndependentTwoMomentGrant
