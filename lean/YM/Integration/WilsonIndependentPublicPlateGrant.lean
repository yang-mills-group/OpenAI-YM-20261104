import YM.Integration.WilsonIndependentLicensedCircuit
import YM.Integration.WilsonIndependentGroupedOrbitBills

/-! Co-select the original unmarked passport and the native regulated infrared accounts. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPublicPlateGrant
open Lattice RG XSpace Precision Source WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Uniform RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum
open RegulatorIR.Profiles RegulatorIR.Calibration RegulatorIR.Taping
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit
open WilsonIndependentEvenPassport (power)
open scoped Classical BigOperators ENNReal NNReal
variable {G:Gauge}{H:Hol G}(R:Master H)(chart:ChartRatio G)(K:KernelChoices)
    (V:XSpace.Run)(e h k j:ℕ)(Y:Program K)(branches:∀ p:Patch,p.Branches K G)
    (p b u:ℕ)(γ:ℝ)(lo:0<γ)(hi:γ<1)

def floor:= WilsonIndependentGroupedShelves.floor G Y (stages j) p (quantum b u) γ lo hi

theorem selected (simple:G.Simple)(valid:LocalRatio chart)(late:5≤j)(head:h+3≤j)(width:p≤u)
    (rate:0<b)(col:G.ColorIndex) :
    ∃ B:WilsonIndependentEvenPassport.Menu R chart K V e h k j (floor (G:=G) K j Y p b u γ lo hi),
      ∀ (z:Requests B.a→ℝ)(money:∀ i,0≤z i),
        let C:=S V B.a B.positive j (by omega)
        let L:=WilsonIndependentGroupedOrbitBills.meter C z money
        let c:=C.leadA Y G (quantum b u)
        SatisfiesQ G Y C branches (stampE C z money) p (quantum b u) γ ∧
        ∃ F:Tent (M V B.a), Notebook C Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p ∧
          (∀ i:Requests B.a,sheet F (Page.opening _ i)=Clocks.flat) ∧
          let T:=C.lane Y G branches (sheet F)
          Cylinder T (C.payroll Y G branches (sheet F)) (C.pushP Y G) (C.takeP Y G) L c p b u ∧
            Lantern (C.dialect Y G branches (sheet F)) (RegulatorIR.FVAAlt2.Rocket.native _) L c γ ∧ T.Endings L := by
  obtain ⟨B⟩:=WilsonIndependentEvenPassport.purchased R chart K V e h k j simple valid branches head late (floor (G:=G) K j Y p b u γ lo hi)
  refine ⟨B,?_⟩
  intro z money C L c
  have grades (m:ℕ) (hm:m∈stages j) : 5≤m :=by simp [stages] at hm;omega
  have numeric (f:Flap (M V B.a)) := B.pre.trans (lengths V B.a j B.positive (by omega:4≤j) f)
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

end YM.Integration.WilsonIndependentPublicPlateGrant
