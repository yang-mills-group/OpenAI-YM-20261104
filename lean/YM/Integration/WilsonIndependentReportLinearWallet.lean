import YM.Integration.WilsonIndependentPublicReportedPeriod

/-! The one unmarked inverse changes a complete complex scalar, including all
thermal convolution terms of the already filed physical source. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentReportLinearWallet
open Lattice RG XSpace XSpace.Rose XSpace.Cirrus Precision Source PertExtension
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Uniform RegulatorIR.Epoch RegulatorIR.Epoch.League
open RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration RegulatorIR.Taping RegulatorIR.Prim
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit
open WilsonIndependentRawNamedProduct WilsonIndependentMatchedNamedPair
open WilsonIndependentPublicReportComplex (row)
open scoped Classical ENNReal NNReal BigOperators PowerSeries

variable {G:Gauge}
    {H:Hol G}(P:Master H)(chart:ChartRatio G)(K:KernelChoices)(V:XSpace.Run)
    (e h k j:ℕ)(Y:Program K)(branches:∀ p:Patch,p.Branches K G)
    (p b u:ℕ)(γ:ℝ)(extra:ℕ)(col:G.ColorIndex)(late:4 ≤ j)
    (B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)

theorem original (good:G.Simple)
    (paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y branches
      p b u γ extra col late B)(q:ℕ)(hq:q≤p)(D:ℕ):
    let C:=S V B.a B.positive j late
    ∃H:ℝ,0≤H ∧ ∃s:ℕ,∀ (F:Tent (M V B.a)),
      Notebook C Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p →
      ∀ (w:Requests B.a)(A A':PowerSeries ℂ)(E:ℝ),
      (∀i,i≤q→‖PowerSeries.coeff i A-PowerSeries.coeff i A'‖≤E) →
      let scale:=F (WilsonIndependentExactPlate.report V B.a w)
      ‖PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply scale D A)-
        PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply scale D A')‖ ≤
        E*(H*(1+Real.log ((V.step w.val).p.side.val:ℝ))^s):=by
  intro C
  obtain ⟨fee,hfee,s,window⟩:=WilsonIndependentPublicClockWindow.original P chart K V e h k j Y
    branches p b u γ extra col late B good paid q hq D
  refine ⟨(q+1:ℕ)*fee,by positivity,s,?_⟩
  intro F book w A A' E bound scale
  let page:=WilsonIndependentExactPlate.report V B.a w
  let μ:ℝ:=(V.step w.val).p.side.val
  let L:=1+Real.log μ
  have hE:0≤E:=(norm_nonneg _).trans (bound 0 (Nat.zero_le _))
  have width:|Real.log (C.l page)|≤Real.log μ:=WilsonIndependentExactReportWidth.logarithm V B.a j B.positive late w
  have lo:1≤μ:=by dsimp [μ];exact_mod_cast (V.step w.val).p.side.pos
  have pos:0≤L:=by dsimp [L];linarith [Real.log_nonneg lo]
  have meter (i:ℕ):‖row scale D q i‖ ≤ fee*L^s:=by
    have ear:=window F book page (PowerSeries.X^i) 1 (fun a _=>by rw [PowerSeries.coeff_X_pow];split <;> simp)
    change ‖PowerSeries.coeff q (WilsonIndependentPublicReportClock.cleared (F page) D (PowerSeries.X ^ i))‖ ≤ _
    apply (show _≤fee*(1+|Real.log (C.l page)|)^s from by simpa only [C,mul_one] using ear).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by dsimp [L];linarith) _) hfee
  rw [WilsonIndependentPublicReportComplex.difference]
  calc
    _≤∑i∈Finset.range (q+1),‖(PowerSeries.coeff i A-PowerSeries.coeff i A')*(row scale D q i:ℂ)‖:=norm_sum_le _ _
    _≤∑_i∈Finset.range (q+1),E*(fee*L^s):=by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,Complex.norm_real]
      exact mul_le_mul (bound i (by have h:=Finset.mem_range.mp hi;omega)) (meter i) (norm_nonneg _) hE
    _=_:=by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];dsimp [L,μ];ring

end YM.Integration.WilsonIndependentReportLinearWallet
