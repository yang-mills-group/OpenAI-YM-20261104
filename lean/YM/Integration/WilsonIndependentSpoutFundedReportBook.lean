import YM.Integration.WilsonIndependentSpoutMarkJourney
import YM.Integration.WilsonIndependentPublicRosterBook

/-! The full orbit-period bill is issued on the same dated notebook as the authentic normalized Mer recursion. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutFundedReportBook
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open WilsonCoeffUV WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonCoeffUV.Blue WilsonCoeffUV.Power RegulatorIR.Ward RegulatorIR.Clocks RegulatorIR.Clocks.Warp WilsonIndependentExactPlate WilsonIndependentLicensedCircuit
open WilsonIndependentSpoutPayrollRoute (reported)
open WilsonIndependentSpoutFundedClocks (clock)
open scoped Classical
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(K:KernelChoices)
    (Y:Program K)(Z:∀P:Patch,P.Branches K G)(V:XSpace.Run)
    {H:Hol G}(P:Master H)(chart:ChartRatio G)(e h k j p b u:ℕ)(γ:ℝ)(hi:γ<1)
    (extra:ℕ)(col:G.ColorIndex)(late:4≤j)(B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)

include hi

theorem priced (simple:G.Simple)(rate:0<b)
    (paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y Z p b u γ extra col late B)
    (D:Tent (M V B.a))(book:Notebook (S V B.a B.positive j late) Y G Z col (RegulatorIR.FVAAlt2.Rocket.native _) D p)
    (ap:Requests B.a→ℝ)(pos:∀w,0≤ap w):
    WilsonIndependentPublicRosterBook.Priced R W K Y Z V B.a j B.positive late p γ ap D:=by
  let C:=S V B.a B.positive j late
  have starts(w:Requests B.a):C.l (Page.opening _ w)=1:=(units V B.a B.positive j late w).1
  have flat(w:Requests B.a):sheet D (Page.opening _ w)=Clocks.flat:=by
    change (D (Page.opening _ w)).scale=_
    rw [show D (Page.opening _ w)=Calibration.dawn from book.reference w]
    exact RegulatorIR.FVAAlt2.Rocket.still
  exact WilsonIndependentPublicRosterBook.appointed R W K Y Z V P chart e h k j p b u γ hi extra late B ap pos D flat
    (WilsonIndependentGroupedOrbitBills.original G Y Z C ap pos D col simple (paid ap pos).1 starts book rate
       (V.finalSide.side.val*V.ratio^B.a) (WilsonIndependentLicensedCircuit.ends V B.a B.positive))

theorem original (simple:G.Simple)(rate:0<b)
    (paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y Z p b u γ extra col late B)
    (A:Requests B.a→Levels G)(s:Requests B.a→ℕ)
    (inc:∀w,WilsonIndependentPublicFreeTrain.Matches (A w) (S V B.a B.positive j late) K (s w) w):
    let C:=S V B.a B.positive j late
    ∃D:Tent (M V B.a),
      (∀c:G.ColorIndex,Notebook C Y G Z c (RegulatorIR.FVAAlt2.Rocket.native _) D p) ∧
      (∀v,RegulatorIR.Clocks.Matches p ((C.payroll Y G Z (sheet D)).bulk v) (reported A s v)) ∧
      (∀v,Squares p (tale (D v).dine) (clock A (XSpace.Bare.chart G) s v) ∧
         Squares p (tale (sheet D v).beta) (((clock A (XSpace.Bare.chart G) s v)⁻¹)^2)) ∧
      (∀(f:Flap (M V B.a))(n:Side),WilsonIndependentSpoutMeasuredHearing.Hearing C Z D f (A f.volW) (s f.volW) p n) ∧
      (∀f,WilsonIndependentNotebookMarkedEdge.Reads C Y Z D A s p f) ∧
      ∀(ap:Requests B.a→ℝ)(_pos:∀w,0≤ap w),
        WilsonIndependentPublicRosterBook.Priced R W K Y Z V B.a j B.positive late p γ ap D:=by
  intro C
  obtain ⟨D,books,quiet,clocks,ears,rows⟩:=WilsonIndependentNotebookMarkedEdge.selected C Y Z A s simple inc p
  exact ⟨D,books,quiet,clocks,ears,rows,
    priced R W K Y Z V P chart e h k j p b u γ hi extra col late B simple rate paid D (books col)⟩

end YM.Integration.WilsonIndependentSpoutFundedReportBook
