import YM.Integration.WilsonIndependentPaidRosterStops
import YM.Integration.WilsonIndependentPublicRosterBook
import YM.Integration.WilsonIndependentReportLinearWallet
import YM.Integration.WilsonIndependentWardSquareLog

/-! The independent period error of a finite product in the actual reporting coupling. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentReportedRosterStops
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

theorem original (good:G.Simple)(paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y branches
    p b u (3/4) extra col late B)(ap:Requests B.a → ℝ)(positive:∀w,0 ≤ ap w)(F:Tent (M V B.a))
    (book:Notebook (S V B.a B.positive j late) Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p)

    (rate:0<b)(clock:∀w,sheet F (Page.opening _ w)=Clocks.flat)
    (I:Type)(σ:I → Bool)(d:I → ℕ)(key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)
    (sample:Requests B.a → Sample 2)(sites:Requests B.a → I → Cover)(x:Requests B.a → Room)(c₀:ℝ)
    (board:∀w,(sample w).F=V.step w.val)
    (reach:∀w,WilsonIndependentRawRosterBudget.span (x w) (sites w) arms ≤ ap w)
    (clear:0<c₀)(safe:((S V B.a B.positive j late).dialect Y G branches (sheet F)).cushion c₀ x)

    (q:ℕ)(hq:q ≤ p)(D:ℕ):
    let C:=S V B.a B.positive j late
    let L:=WilsonIndependentGroupedOrbitBills.meter C ap positive
    let sky:=C.dialect Y G branches (sheet F)
    ∃A:ℝ,0 ≤ A ∧ ∃v s:ℕ,∀(stop:Choice (M V B.a))(w:Requests B.a),
      let scale:=F (WilsonIndependentExactPlate.report V B.a w)
      let Z:=Bare.normalized (W.tree (sample w).F.p) G (film R W σ d key (sample w) (sites w) arms)
      let X:PowerSeries ℂ:=PowerSeries.mk fun i=>(note
        ((WilsonIndependentRawRosterOrbit.report R W σ d key arms
          (C.payroll Y G branches (sheet F)) sites).main (stop.choose w) i 0):ℂ)
      let μ:ℝ:=(V.step w.val).p.side.val
      ‖PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply scale D Z)-
        PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply scale D X)‖ ≤
        A*(L.val w).toReal^v*(1+Real.log μ)^s*sky.modifyErr 0 b (3/4) stop w:=by
  intro C L sky
  obtain ⟨pre,_⟩:=paid ap positive
  have opening (w:Requests B.a):C.l (Page.opening _ w)=1:=(units V B.a B.positive j late w).1
  obtain ⟨cylinder,lamp,ends⟩:=WilsonIndependentGroupedOrbitBills.original G Y branches C ap positive F col
    good pre opening book rate (V.finalSide.side.val*V.ratio^B.a)
    (WilsonIndependentLicensedCircuit.ends V B.a B.positive)
  have hside(w:Requests B.a):TopF (n V B.a) w=(sample w).F.p.side:=by
    rw [board w]; exact WilsonIndependentExactPlate.starting V B.a w
  have fare (w:Requests B.a): ENNReal.ofReal (1+WilsonIndependentRawRosterBudget.span (x w) (sites w) arms) ≤ L.val w:=by
    apply le_trans _ le_self_add
    exact ENNReal.ofReal_le_ofReal (by linarith [reach w])
  have fixed(i:Fin (q+1)):=WilsonIndependentPaidRosterStops.original R W σ d key arms sites cylinder lamp ends
    sample x opening clock hside fare clear safe i (by omega)
  choose charge hc exponent raw using fixed
  obtain ⟨fee,hfee,s,window⟩:=WilsonIndependentReportLinearWallet.original P chart K V e h k j Y
    branches p b u (3/4) extra col late B good paid q hq D
  let cash:=∑a,charge a
  let degree:=∑a,exponent a
  have cm:0≤cash:=Finset.sum_nonneg (fun a _=>hc a)
  refine ⟨cash*fee,mul_nonneg cm hfee,degree,s,?_⟩
  intro stop w scale Z X μ
  let size:ℝ:=(L.val w).toReal
  let err:=sky.modifyErr 0 b (3/4) stop w
  have hsize:1 ≤ size:=by
    have h:=ENNReal.toReal_mono (L.below w) (L.above w)
    simpa only [ENNReal.toReal_one] using h
  have hμ:1 ≤ μ:=by dsimp only [μ];exact_mod_cast (V.step w.val).p.side.pos
  have he:0 ≤ err:=
    add_nonneg (sky.transfer_pos w).le (inv_nonneg.mpr (Real.rpow_nonneg (sky.hl _).le _))
  have tested(i:ℕ)(hi:i ≤ q):‖PowerSeries.coeff i Z-PowerSeries.coeff i X‖ ≤ cash*size^degree*err:=by
    let a:Fin (q+1):=⟨i,by omega⟩
    simp only [X,PowerSeries.coeff_mk,Z]
    apply (raw a stop (fun _=>Nat.zero_le _) w).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (Finset.single_le_sum (fun a _=>hc a) (Finset.mem_univ a))
      (pow_le_pow_right₀ hsize (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ a)))
      (pow_nonneg (zero_le_one.trans hsize) _) cm) he
  have answer:=window F book w Z X (cash*size^degree*err) tested
  exact answer.trans_eq (by dsimp only [size,err]; ring)

end YM.Integration.WilsonIndependentReportedRosterStops
