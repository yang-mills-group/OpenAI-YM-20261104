import YM.Integration.WilsonIndependentPublicRawBook
import YM.RegulatorIR.Venture.Gardens

/-! The unmarked clock on the very Notebook that reads a moving source.
Its upper price is fixed at zero aperture before choosing that Notebook. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentPublicReportClockBill
open Lattice RG XSpace Precision Source WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Uniform RegulatorIR.Epoch RegulatorIR.Epoch.League
open RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration RegulatorIR.Taping RegulatorIR.Venture
open RegulatorIR.Prim WilsonIndependentExactPlate WilsonIndependentLicensedCircuit
open scoped Classical ENNReal NNReal BigOperators
variable {G:Gauge}{H:Hol G}(P:Master H)(chart:ChartRatio G)(K:KernelChoices)
    (V:XSpace.Run)(e h k j:ℕ)(Y:Program K)(branches:∀ p:Patch,p.Branches K G)
    (p b u:ℕ)(γ:ℝ)(extra:ℕ)(col:G.ColorIndex)(late:4≤j)
    (B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)

theorem original (good:G.Simple)
    (paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y branches
      p b u γ extra col late B):
    let C:=S V B.a B.positive j late
    let D:=RegulatorIR.FVAAlt2.Rocket.native (M V B.a)
    ∀ r ≤ p,∃ (fee:ℝ≥0∞)(k:ℕ),fee≠⊤ ∧ ∀F:Tent (M V B.a),
      Notebook C Y G branches col D F p → ∀page:Page (M V B.a),
      ‖biases (sheet F page) r‖ₑ≤ fee*(ENNReal.ofReal (1+|Real.log (C.l page)|))^k:=by
  intro C D
  let zero:Requests B.a→ℝ:=fun _=>0
  have hz:∀w,0≤zero w:=fun _=>le_rfl
  obtain ⟨pre,F₀,book,_,_⟩:=paid zero hz
  have atRef (w:Requests B.a):(stampE C zero hz).peak (D.choose w)=0:=by
    change Real.log (C.l (Page.opening _ w))=0
    rw [(units V B.a B.positive j late w).1,Real.log_one]
  have wallet:=dome C Y G branches (scripts_v G Y C branches pre) pre.θ_pos col good F₀ D atRef book
  intro r hr
  obtain ⟨fee,d,hf,bill⟩:=wallet.2 r hr
  refine ⟨fee,d,hf,?_⟩
  intro F filed page
  have agree:=recognized C Y G branches col filed book page r hr
  change biases (sheet F page) r=biases (sheet F₀ page) r at agree
  rw [agree]
  simpa [Marked.age_t,Marked.credit,Marked.peak,stampE,zero] using bill page

end YM.Integration.WilsonIndependentPublicReportClockBill
