import YM.Integration.WilsonIndependentPublicClockTransfer
import YM.Integration.WilsonIndependentPublicReportClockBill

/-! On the elected finite circuit, the covariance budget for the
unmarked report is selected before every moving source and every stop. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentPublicClockWindow
open Lattice RG XSpace Precision Source WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Uniform RegulatorIR.Epoch RegulatorIR.Epoch.League
open RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration RegulatorIR.Clocks
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit
open WilsonIndependentPublicReportClock WilsonIndependentPublicReportBias
open scoped Classical ENNReal NNReal BigOperators
variable {G:Gauge}{H:Hol G}(P:Master H)(chart:ChartRatio G)(K:KernelChoices)
    (V:XSpace.Run)(e h k j:ℕ)(Y:Program K)(branches:∀ p:Patch,p.Branches K G)
    (p b u:ℕ)(γ:ℝ)(extra:ℕ)(col:G.ColorIndex)(late:4≤j)
    (B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)

theorem original (good:G.Simple)
    (paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y branches
      p b u γ extra col late B)(q:ℕ)(hq:q ≤ p)(D:ℕ):
    let C:=S V B.a B.positive j late
    let D₀:=RegulatorIR.FVAAlt2.Rocket.native (M V B.a)
    ∃ fee:ℝ,0≤fee ∧ ∃ d:ℕ,∀F:Tent (M V B.a),
      Notebook C Y G branches col D₀ F p → ∀ (page:Page (M V B.a))(Z:Writing)(E:ℝ),
      (∀ r,r ≤ q → ‖PowerSeries.coeff r Z‖≤E) →
      ‖PowerSeries.coeff q (cleared (F page) D Z)‖≤fee*(1+|Real.log (C.l page)|)^d*E:=by
  intro C D₀
  have book:=WilsonIndependentPublicReportClockBill.original P chart K V e h k j Y
    branches p b u γ extra col late B good paid
  choose a d fin pay using fun i:Fin (q+1)=>book i (by omega)
  obtain ⟨M₀,hM,s,spend⟩:=WilsonIndependentPublicClockTransfer.income q D
  let gross:=1+∑ i,(a i).toReal
  let degree:=∑ i,d i
  have hm:1≤gross:=by
    change 1≤1+∑ i,(a i).toReal
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _=>ENNReal.toReal_nonneg))
  refine ⟨M₀*gross^s,mul_nonneg hM (pow_nonneg (by linarith) _),degree*s,?_⟩
  intro F filed page Z E bound
  let t:ℝ:=1+|Real.log (C.l page)|
  have ht:1≤t:=le_add_of_nonneg_right (abs_nonneg _)
  have ht':0≤t:=by linarith
  have priced (r:ℕ)(hr:r ≤ q): ‖PowerSeries.coeff r (beta (F page))‖≤gross*t^degree:=by
    let i:Fin (q+1):=⟨r,by omega⟩
    have v:=pay i F filed page
    have hfinite: a i*(ENNReal.ofReal t)^d i≠⊤:=
      ENNReal.mul_ne_top (fin i) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    have vr:=ENNReal.toReal_mono hfinite v
    have vb:‖PowerSeries.coeff r (beta (F page))‖≤(a i).toReal*t^d i:=by
      change ‖biases (sheet F page) (i:ℕ)‖≤_
      simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal ht',ENNReal.toReal_pow,toReal_enorm] using vr
    have hm':(a i).toReal≤gross:=by
      have f: (a i).toReal≤∑ l,(a l).toReal:=Finset.single_le_sum
        (fun l (_:l∈(Finset.univ:Finset (Fin (q+1))))=>ENNReal.toReal_nonneg) (Finset.mem_univ i)
      change (a i).toReal ≤ 1+∑ l,(a l).toReal
      linarith
    have hd:d i≤degree:=Finset.single_le_sum (fun l _=>Nat.zero_le (d l)) (Finset.mem_univ i)
    exact vb.trans (mul_le_mul hm' (pow_le_pow_right₀ ht hd) (pow_nonneg ht' _) (by linarith))
  have z:=spend (F page) (gross*t^degree) (one_le_mul_of_one_le_of_one_le hm (one_le_pow₀ ht))
    priced Z E bound
  simpa only [mul_pow,←pow_mul,mul_assoc] using z

end YM.Integration.WilsonIndependentPublicClockWindow
