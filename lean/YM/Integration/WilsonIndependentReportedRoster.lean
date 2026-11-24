import YM.Integration.WilsonIndependentPublicRosterBook
import YM.Integration.WilsonIndependentReportLinearWallet
import YM.Integration.WilsonIndependentWardSquareLog

/-! The independent period error of a finite product in the actual reporting coupling. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentReportedRoster
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit WilsonIndependentRawRosterWord
open scoped Classical ENNReal NNReal BigOperators PowerSeries
variable {G:Gauge} (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    {H:Hol G}(P:Master H)(chart:ChartRatio G)(K:KernelChoices)(V:XSpace.Run)
    (e h k j:ℕ)(Y:Program K)(branches:∀p:Patch,p.Branches K G)(p b u extra:ℕ)
    (col:G.ColorIndex)(late:4 ≤ j)(B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)

theorem appointed (good:G.Simple)(paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y branches
    p b u (3/4) extra col late B)(ap:Requests B.a → ℝ)(positive:∀w,0 ≤ ap w)(F:Tent (M V B.a))
    (book:Notebook (S V B.a B.positive j late) Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p)
    (orbit:WilsonIndependentPublicRosterBook.Priced R W K Y branches V B.a j B.positive late p (3/4) ap F)
    (I:Type)(σ:I → Bool)(d:I → ℕ)(key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)
    (sample:Requests B.a → Sample 2)(sites:Requests B.a → I → Cover)(x:Requests B.a → Room)(c₀:ℝ)
    (board:∀w,(sample w).F=V.step w.val)
    (reach:∀w,WilsonIndependentRawRosterBudget.span (x w) (sites w) arms ≤ ap w)
    (clear:0<c₀)(safe:((S V B.a B.positive j late).dialect Y G branches (sheet F)).cushion c₀ x)
    (q:ℕ)(hq:q ≤ p)(D:ℕ)(band:ℝ)(hband:0<band)
    (sq:∀w,(Real.log (1+ap w))^2 ≤ band*Real.log ((V.step w.val).p.side.val:ℝ)):
    let C:=S V B.a B.positive j late
    ∃A:ℝ,0 ≤ A ∧ ∃v:ℕ,∀w:Requests B.a,
      let scale:=F (WilsonIndependentExactPlate.report V B.a w)
      let Z:=Bare.normalized (W.tree (sample w).F.p) G (film R W σ d key (sample w) (sites w) arms)
      let X:PowerSeries ℂ:=PowerSeries.mk fun i=>(note
        ((WilsonIndependentRawRosterOrbit.report R W σ d key arms
          (C.payroll Y G branches (sheet F)) sites).main (Page.finallyW (M V B.a) w) i 0):ℂ)
      let μ:ℝ:=(V.step w.val).p.side.val
      ‖PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply scale D Z)-
        PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply scale D X)‖ ≤
        A*(1+Real.log μ)^v*μ^(-(1/4:ℝ)):=by
  intro C
  obtain ⟨fee,hfee,s,window⟩:=WilsonIndependentReportLinearWallet.original P chart K V e h k j Y
    branches p b u (3/4) extra col late B good paid q hq D
  have earned:=orbit I σ d key arms sample sites x c₀ board reach clear safe
  choose k₀ m₀ hm pr using fun i:Fin (q+1)=>earned i (by omega)
  let cash:=∑i,m₀ i
  let v:=∑i,k₀ i
  let E:=Real.exp ((v:ℝ)^2/(4*((1/8:ℝ)/band)))
  have cm:0 ≤ cash:=Finset.sum_nonneg (fun i _=>hm i)
  refine ⟨fee*(cash*E),mul_nonneg hfee (mul_nonneg cm (Real.exp_pos _).le),s+v,?_⟩
  intro w scale Z X μ
  let L:ℝ:=1+ap w+Real.log μ
  have unit:1 ≤ μ:=by dsimp only [μ]; exact_mod_cast (V.step w.val).p.side.pos
  have lm:=Real.log_nonneg unit
  have one:1 ≤ L:=by dsimp [L];linarith [positive w]
  have μ₀:=zero_le_one.trans unit
  let raw:=cash*L^v*μ^(-(3/8:ℝ))
  have tested(i:ℕ)(hi:i ≤ q):‖PowerSeries.coeff i Z-PowerSeries.coeff i X‖ ≤ raw:=by
    let a:Fin (q+1):=⟨i,by omega⟩
    have h:=pr a w
    rw [show (-((3/4)/2):ℝ)=-(3/8) by norm_num] at h
    have ee:‖PowerSeries.coeff i Z-PowerSeries.coeff i X‖ ≤ m₀ a*L^(k₀ a)*μ^(-(3/8:ℝ)):=by
      simpa only [a,Z,X,C,PowerSeries.coeff_mk,L,μ] using h
    apply ee.trans (mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg μ₀ _))
    exact mul_le_mul (Finset.single_le_sum (fun i _=>hm i) (Finset.mem_univ a))
      (pow_le_pow_right₀ one (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ a)))
      (pow_nonneg (zero_le_one.trans one) _) cm
  have pay:raw ≤ (cash*E)*(1+Real.log μ)^v*μ^(-(1/4:ℝ)):=by
    have line:=WilsonIndependentWardSquareLog.restored v band hband 1 cash μ (ap w) raw
      zero_le_one cm unit (positive w) (sq w) (by simp [raw,L])
    simpa only [one_mul] using line
  have actual:=window F book w Z X raw tested
  calc
    _ ≤ raw*(fee*(1+Real.log μ)^s):=actual
    _ ≤ ((cash*E)*(1+Real.log μ)^v*μ^(-(1/4:ℝ)))*(fee*(1+Real.log μ)^s):=
      mul_le_mul_of_nonneg_right pay (mul_nonneg hfee (pow_nonneg (by linarith) _))
    _ = _:=by rw [pow_add];ring
end YM.Integration.WilsonIndependentReportedRoster
