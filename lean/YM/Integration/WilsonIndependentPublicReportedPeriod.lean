import YM.Integration.WilsonIndependentPublicReportedOrbit
import YM.Integration.WilsonIndependentExactReportWidth
import YM.Integration.WilsonIndependentWardSquareLog

/-! Apply the actual report to both sides of the finite Wilson-orbit
comparison. The unmarked clock price precedes selection of the exterior. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentPublicReportedPeriod
open Lattice RG XSpace XSpace.Rose XSpace.Cirrus Precision Source PertExtension
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Uniform RegulatorIR.Epoch RegulatorIR.Epoch.League
open RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration RegulatorIR.Taping RegulatorIR.Prim
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit
open WilsonIndependentRawNamedProduct WilsonIndependentMatchedNamedPair
open WilsonIndependentPublicReportComplex (row)
open scoped Classical ENNReal NNReal BigOperators PowerSeries

variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    {H:Hol G}(P:Master H)(chart:ChartRatio G)(K:KernelChoices)(V:XSpace.Run)
    (e h k j:ℕ)(Y:Program K)(branches:∀ p:Patch,p.Branches K G)
    (p b u:ℕ)(extra:ℕ)(col:G.ColorIndex)(late:4 ≤ j)
    (B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)

def difference (F:Tent (M V B.a))(l r:Bool)(a a' q D:ℕ)
    (left:(R.family.labels.level a).Index)(right:(R.family.labels.level a').Index)
    (sample:Requests B.a → Sample 2)(o z:Requests B.a → Cover)(w:Requests B.a):ℂ:=
  let C:=S V B.a B.positive j late
  let page:=WilsonIndependentExactPlate.report V B.a w
  let full:=Bare.normalized (W.tree (sample w).F.p) G
    (printed R W (sample w) l a (o w) left*printed R W (sample w) r a' (z w) right)
  let stop:ℂ⟦X⟧:=PowerSeries.mk fun i=>(note ((WilsonIndependentRawNamedProduct.report
    R W l r a a' left right (C.payroll Y G branches (sheet F)) o z).main
    (Page.finallyW (M V B.a) w) i 0):ℂ)
  PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply (F page) D full)-
    PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply (F page) D stop)

theorem original (good:G.Simple)
    (paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y branches
      p b u (3/4) extra col late B)(q:ℕ)(hq:q ≤ p)(D:ℕ):
    let C:=S V B.a B.positive j late
    ∀(aperture:Requests B.a → ℝ)(_positive:∀w,0 ≤ aperture w)
      (F:Tent (M V B.a))(_book:Notebook C Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p),
    WilsonIndependentPublicRawOrbit.Priced R W K Y branches V B.a j B.positive late p (3/4) aperture F →
    ∀(l r:Bool)(a a':ℕ)(left:(R.family.labels.level a).Index)(right:(R.family.labels.level a').Index)
      (sample:Requests B.a → Sample 2)(o z:Requests B.a → Cover)(x:Requests B.a → Room)(c₀:ℝ),
      (∀w,(sample w).F=V.step w.val) → (∀w,WilsonIndependentRawPairOpening.span x o z w ≤ aperture w) →
      0<c₀ → (C.dialect Y G branches (sheet F)).cushion c₀ x →
    ∀ band:ℝ,0<band → (∀w,(Real.log (1+aperture w))^2 ≤ band*Real.log ((V.step w.val).p.side.val:ℝ)) →
    ∃ C₀:ℝ,0 ≤ C₀ ∧ ∃ k₀:ℕ,∀w,
      ‖difference R W P chart K V e h k j Y branches extra late B F l r a a' q D left right sample o z w‖ ≤
        C₀*(1+Real.log ((V.step w.val).p.side.val:ℝ))^k₀*((V.step w.val).p.side.val:ℝ)^(-(1/4:ℝ)):=by
  intro C ap positive F book orbit l r a a' left right samples o z x c₀ board reach clear safe band hband square
  obtain ⟨fee,hfee,d,price⟩:=WilsonIndependentPublicReportedOrbit.appointed R W P chart K V e h k j Y branches
    p b u (3/4) extra col late B good paid q hq D
  obtain ⟨H₀,hH,s,ear⟩:=price ap positive F book orbit l r a a' left right samples o z x c₀ board reach clear safe
  let E:=Real.exp ((s:ℝ)^2/(4*((1/8:ℝ)/band)))
  refine ⟨fee*(H₀*E),mul_nonneg hfee (mul_nonneg hH (Real.exp_pos _).le),d+s,?_⟩
  intro w
  let μ:ℝ:=(V.step w.val).p.side.val
  let page:=WilsonIndependentExactPlate.report V B.a w
  have unit:1 ≤ μ:=by
    dsimp only [μ]
    exact_mod_cast (show 1 ≤ (V.step w.val).p.side.val from (V.step w.val).p.side.pos)
  have lm:=Real.log_nonneg unit
  have lw:|Real.log (C.l page)| ≤ Real.log μ:=WilsonIndependentExactReportWidth.logarithm V B.a j B.positive late w
  let raw:=H₀*(1+ap w+Real.log μ)^s*μ^(-(3/8:ℝ))
  have gross:0 ≤ raw:=mul_nonneg (mul_nonneg hH (pow_nonneg (by linarith [positive w]) _))
    (Real.rpow_nonneg (zero_le_one.trans unit) _)
  have pay:raw ≤ (H₀*E)*(1+Real.log μ)^s*μ^(-(1/4:ℝ)):=by
    have line:=WilsonIndependentWardSquareLog.restored s band hband 1 H₀ μ (ap w) raw
      zero_le_one hH unit (positive w) (square w) (by simp [raw])
    simpa only [one_mul] using line
  have measured:=ear w page
  dsimp only at measured
  rw [show (-(3/4/2):ℝ)= -(3/8:ℝ) by norm_num] at measured
  change _ ≤ fee*(1+|Real.log (C.l page)|)^d*raw at measured
  apply measured.trans
  calc
    fee*(1+|Real.log (C.l page)|)^d*raw ≤ fee*(1+Real.log μ)^d*raw :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith) _) hfee) gross
    _ ≤ (fee*(1+Real.log μ)^d)*((H₀*E)*(1+Real.log μ)^s*μ^(-(1/4:ℝ))) :=
      mul_le_mul_of_nonneg_left pay (mul_nonneg hfee (pow_nonneg (by linarith) _))
    _ = _ := by change _ = fee*(H₀*E)*(1+Real.log μ)^(d+s)*μ^(-(1/4:ℝ));rw [pow_add]; ring

end YM.Integration.WilsonIndependentPublicReportedPeriod
