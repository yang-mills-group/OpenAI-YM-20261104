import YM.Integration.WilsonIndependentRawRosterOrbit
import YM.Integration.WilsonIndependentPublicRawBook

/-! The same book buys the complete ordinary word for every finite roster
and its signed two-field determining rows on the matched inversion board. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentPublicRosterBook
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit WilsonIndependentRawRosterWord
open scoped Classical ENNReal NNReal
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(K:KernelChoices)
    (Y:Program K)(branches:∀p:Patch,p.Branches K G)(V:XSpace.Run)(a j:ℕ)(ha:0<a)(late:4 ≤ j)

def Priced (p:ℕ)(γ:ℝ)(aperture:Requests a → ℝ)(F:Tent (M V a)):Prop:=
  let C:=S V a ha j late
  ∀ (I:Type)(σ:I → Bool)(d:I → ℕ)(key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)
    (sample:Requests a → Sample 2)(sites:Requests a → I → Cover)(x:Requests a → Room)(c₀:ℝ),
    (∀w,(sample w).F=V.step w.val) →
    (∀w,WilsonIndependentRawRosterBudget.span (x w) (sites w) arms ≤ aperture w) →
    0<c₀ → (C.dialect Y G branches (sheet F)).cushion c₀ x →
    ∀q:ℕ,q ≤ p → ∃ k₀:ℕ,∃ H₀:ℝ,0 ≤ H₀ ∧ ∀w,
      ‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
        (film R W σ d key (sample w) (sites w) arms))-
        (note ((WilsonIndependentRawRosterOrbit.report R W σ d key arms
          (C.payroll Y G branches (sheet F)) sites).main (Page.finallyW (M V a) w) q 0):ℂ)‖ ≤
        H₀*(1+aperture w+Real.log ((V.step w.val).p.side.val:ℝ))^k₀*((V.step w.val).p.side.val:ℝ)^(-(γ/2))

variable {H:Hol G}(P:Master H)(chart:ChartRatio G)(e h k j p b u:ℕ)(γ:ℝ)(hi:γ<1)
    (extra:ℕ)(col:G.ColorIndex)(late:4 ≤ j)(B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)
include hi in
theorem appointed (ap:Requests B.a → ℝ)(positive:∀w,0 ≤ ap w)(F:Tent (M V B.a))
    (clock:∀w,sheet F (Page.opening _ w)=Clocks.flat)
    (paid:let C:=S V B.a B.positive j late
          let L:=WilsonIndependentGroupedOrbitBills.meter C ap positive
          let cash:=C.leadA Y G (quantum b u)
          let T:=C.lane Y G branches (sheet F)
          Cylinder T (C.payroll Y G branches (sheet F)) (C.pushP Y G) (C.takeP Y G) L cash p b u ∧
            Lantern (C.dialect Y G branches (sheet F)) (RegulatorIR.FVAAlt2.Rocket.native _) L cash γ ∧
            T.Endings L):
    Priced R W K Y branches V B.a j B.positive late p γ ap F:=by
  let C:=S V B.a B.positive j late
  let L:=WilsonIndependentGroupedOrbitBills.meter C ap positive
  obtain ⟨cylinder,lamp,ends⟩:=paid
  intro I σ d key arms sample sites x c₀ board reach clear safe q hq
  have opening(w:Requests B.a):C.l (Page.opening _ w)=1:=(units V B.a B.positive j late w).1
  have same(w:Requests B.a):TopF (n V B.a) w=(sample w).F.p.side:=by
    rw [board w]
    exact WilsonIndependentExactPlate.starting V B.a w
  have fare(w:Requests B.a):ENNReal.ofReal (1+WilsonIndependentRawRosterBudget.span (x w) (sites w) arms) ≤ L.val w:=by
    apply le_trans _ le_self_add
    exact ENNReal.ofReal_le_ofReal (by linarith [reach w])
  obtain ⟨H₀,k₀,hH,ear⟩:=WilsonIndependentRawRosterOrbit.terminal R W σ d key arms sites
    cylinder lamp ends sample x opening clock same fare clear safe q hq hi (V.finalSide.side.val*V.ratio^B.a)
    (WilsonIndependentLicensedCircuit.ends V B.a B.positive)
  refine ⟨k₀,H₀,hH,fun w=>?_⟩
  have side:1 ≤ ((V.step w.val).p.side.val:ℝ):=by exact_mod_cast (V.step w.val).p.side.pos
  have meter:(L.val w).toReal=1+ap w+Real.log ((V.step w.val).p.side.val:ℝ):=by
    change (ENNReal.ofReal (1+ap w)+ENNReal.ofReal (Real.log ((V.step w.val).p.side.val:ℝ))).toReal=_
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith [positive w]),ENNReal.toReal_ofReal (Real.log_nonneg side)]
  have result:=ear w
  change _ ≤ H₀*(L.val w).toReal^k₀*((V.step w.val).p.side.val:ℝ)^(-(γ/2)) at result
  rw [meter] at result
  exact result

include hi in
theorem original (paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y branches
    p b u γ extra col late B):
    ∀(ap:Requests B.a → ℝ)(_positive:∀w,0 ≤ ap w),
      let C:=S V B.a B.positive j late
      ∃F:Tent (M V B.a),Notebook C Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p ∧
        (∀w,sheet F (Page.opening _ w)=Clocks.flat) ∧
        WilsonIndependentPublicRawOrbit.Priced R W K Y branches V B.a j B.positive late p γ ap F ∧
        Priced R W K Y branches V B.a j B.positive late p γ ap F:=by
  intro ap positive C
  obtain ⟨_,F,book,clock,sale⟩:=paid ap positive
  exact ⟨F,book,clock,WilsonIndependentPublicRawBook.notebook R W K Y branches V P chart e h k j p b u γ hi
    extra late B ap positive F clock sale,
    appointed R W K Y branches V P chart e h k j p b u γ hi extra late B ap positive F clock sale⟩

end YM.Integration.WilsonIndependentPublicRosterBook
