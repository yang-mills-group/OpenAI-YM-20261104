import YM.Integration.WilsonOriginalPublicNodalHelperCircuit
import YM.Integration.WilsonIndependentPublicPlateGrant

/-! The full grouped normalization and common raw price for the chosen, already marked helper Notebook. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingHelperQuote
open Lattice RG Source Labels PertExtension XSpace Precision
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Uniform RegulatorIR.Calibration RegulatorIR.Taping
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open WilsonIndependentLicensedCircuit (stages)
open WilsonOriginalPublicNodalHelperShape (length)
open scoped Classical ENNReal NNReal
variable {G:Gauge}{H:Hol G}(P:Master H)(chart:ChartRatio G)(K:KernelChoices)(V:XSpace.Run)(e h k j extra:ℕ)
    (Y:Program K)(Z:∀p:Patch,p.Branches K G)(p b u:ℕ)(γ:ℝ)(lo:0<γ)(hi:γ<1)
    (B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)
    (simple:G.Simple)(late:5≤j)(width:p≤u)(rate:0<b)
    (paid:WilsonIndependentPublicPlateGrant.floor (G:=G) K j Y p b u γ lo hi ≤ extra)
    {X:Type}(E r:X → ℕ)(res:∀x,r x<B.a)(enough:∀x,0<length E r B.a x)
local notation "C" => WilsonOriginalPublicNodalHelperCircuit.circuit V E r B.a j B.positive (by omega:4≤j)

include simple width rate paid res enough in
theorem original (ap:X → ℝ)(positive:∀x,0≤ap x)(col:G.ColorIndex)
    (F:Tent (length E r B.a))(notes:Notebook (C) Y G Z col (RegulatorIR.FVAAlt2.Rocket.native _) F p):
    let L:=WilsonIndependentGroupedOrbitBills.meter (C) ap positive
    let cash:=(C).leadA Y G (quantum b u)
    let T:=(C).lane Y G Z (sheet F)
    (∀x,sheet F (Page.opening _ x)=Clocks.flat) ∧
      Cylinder T ((C).payroll Y G Z (sheet F)) ((C).pushP Y G) ((C).takeP Y G) L cash p b u ∧
      Lantern ((C).dialect Y G Z (sheet F)) (RegulatorIR.FVAAlt2.Rocket.native _) L cash γ ∧ T.Endings L:=by
  intro L cash T
  have grades (m:ℕ)(atStage:m∈stages j):5 ≤ m:=by simp [stages] at atStage;omega
  have numeric (f:Flap (length E r B.a)):=paid.trans (B.pre.trans
    (WilsonOriginalPublicNodalHelperCircuit.length_le V E r B.a j B.positive (by omega) f))
  have ready:=WilsonIndependentGroupedShelves.original G Y Z (C) (stages j) p (quantum b u) γ lo hi grades
    (show p+2≤quantum b u by unfold quantum;omega) (show 3≤quantum b u by unfold quantum;omega)
    numeric (WilsonIndependentLicensedCircuit.patches V B.a j B.positive (by omega))
    (WilsonOriginalPublicNodalHelperCircuit.page V E r B.a j B.positive (by omega))
    (WilsonOriginalPublicNodalHelperCircuit.patch V E r B.a j B.positive (by omega) res) ap positive
  constructor
  · intro x
    change (F (Page.opening _ x)).scale=_
    rw [show F (Page.opening _ x)=Calibration.dawn from notes.reference x]
    exact RegulatorIR.FVAAlt2.Rocket.still
  · exact WilsonIndependentGroupedOrbitBills.original G Y Z (C) ap positive F col simple ready
      (WilsonOriginalPublicNodalHelperCircuit.opening V E r B.a j B.positive (by omega)) notes rate
      (V.finalSide.side.val*V.ratio^B.a) (WilsonOriginalPublicNodalHelperCircuit.outer V E r B.a B.positive enough)

end YM.Integration.WilsonSeparatedPrefixMovingHelperQuote
end
