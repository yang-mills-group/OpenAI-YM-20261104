import YM.Integration.WilsonOriginalCompanionSpent
import YM.Integration.WilsonOriginalCompanionMaterialPeer
import YM.Integration.WilsonOriginalScalarGallery

/-! The terminal canonical hard withdrawal refunds its named slot with intact ordinary peers at the true α−2 wage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionLowerPeer
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source QuadraticLocal QuadraticLocal.Earn Marker Push
open Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow Motion Bandage Next.Foundations Trace.Physical.GermGraph Pert.Asymptotics
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCompanionFace
open WilsonMeasuredCompanionWage WilsonThermometerUnitFilingCoarse WilsonThermometerSolitaryExchange
open WilsonOriginalCompanionCellRoots WilsonThermometerOwnOffsetJoint WilsonOriginalDepositedHard
open private margin from YM.Integration.WilsonOriginalCompanionMaterialPeer
open Extraction Cells XSpace WilsonThermometerAlignedCells
open scoped Classical BigOperators Topology
local notation "J"=>Stock.census (Fin 3)
variable {G:Gauge}(R:Run G)
local notation "A"=>R.family.path.levels
local notation "C"=>R.family
def tariff:ℝ:=2*WilsonOriginalCompanionSpent.tariff

theorem original (simple:G.Simple)(cater:Cater (C) R.doors)(bank:WilsonThermometerClusterProjectionBudget.Ready (A))
    (book:WilsonReportLampForecast.Ready (A))(φ:Test 3)(c q:ℕ):
    ∀ᶠ j:ℕ in atTop,∀N p f (height:j+2≤f)(_fn:f≤N),(f-(j+2):ℕ)≤(c:ℝ)*Real.log (RG16.Lambda (A) f)+2 →
    0≤((A).budget f).supportExponent-2 → ∀r:ℝ,|r|≤(C).S.a (j+1) →
    ∀y:Site ((C).side N p)×Site ((C).side N p),mass (R:=R) r (N,p) φ y≠0 →
    let o:=origins R (atOrigin y) f
    let P:=(C).path.rep N p f
    let κ:=LocalComparison.forcedDivisor (C) f
    ∀(T I:Type)[Countable I](E:Lamps T I G P.p o (J))(w:Fin 3→ℝ)(v:Fin 3),(∀i,0<w i) →
    (∀b:ℝ,E.Paid (wage v w b) P.p.B (((A).budget f).supportExponent-2) 1) →
    ∀{d:ℕ}{F:Frame G d}(h:Coefficient F ((C).side f p))(hol:Hol G)(S:SectionData F)(B:ℝ),0≤B →
    h.Format (o v) hol P → h.remBound (o v) P κ B → ∀(t:T→ℂ), (∀x,‖t x‖≤1) →
    ∀u:ℕ,(C).ref 0≤u → ∀uj:u≤j,Opened (C) 0 u p → Opened (C) 0 j p →
    ∀(x:T)(s:(J).Mode),v∈s.val →
    let Y:=fun U=>t x*(h.density (o v) S P U-(soft h).density (o v) S P U)*peers E v s x U
    Integrable Y (prior G _) ∧ companions v w s*‖reading R (N:=N) Y u (uj.trans (by omega))‖≤
      tariff*B*(regulatorRun (C) N p f)^q:=by
  obtain ⟨age,reserve⟩:=eventually_atTop.mp (WilsonOriginalCompanionHardCurrency.reserve R simple)
  filter_upwards [WilsonOriginalCompanionSpent.original R simple cater bank book c 81 q,
    WilsonOriginalCompanionCellRoots.original R simple φ,eventually_ge_atTop age] with j sale cells aged
  intro N p f height fn days expo r cols y active o P κ T I inst E w v wp regular d F h hol S B bp fit actual t unit u ref uj ou oj x s inside Y
  let cash:=(A).clock.forcedAllowance f
  let atm:=((R.T.sticks N p).prices f (Nat.zero_le _) fn).1
  let rent:Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent cash:=
    Hard.rentValid atm.valid.labels.forced atm.valid.labels.boundK
  let old:Hard T P.p P.activities.forced P.activities.K o (J):=Hard.rent rent
  let fresh:=joined old v h fit t
  let D:Gallery T I o P (J):=⟨E,fresh⟩
  let O:Gallery T I o P (J):=⟨E,old⟩
  have kp:0<κ:=Real.sqrt_pos.mpr (Real.exp_pos _)
  have actualBudget:cash=κ^2:=(Real.sq_sqrt (Real.exp_pos _).le).symm
  have small:κ≤1:=(reserve f (by omega)).trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _)))
  obtain ⟨home,parent,cover,anchor⟩:=cells N p f height fn r cols y active
  have identity(U):O.density x U=(P.eval U:ℂ) • Poly.pass (E.log x U):=by
    have quiet:O.gas x U=Poly.bead (J) (P.activities.gas P.p U:ℂ):=
      WilsonOriginalScalarGallery.gas (o:=o) (Γ:=(J)) rent wp x U
    change (Real.exp (P.exponent U):ℂ) • (_*O.gas x U)=_
    rw [quiet,mul_comm _ (Poly.bead _ _),Poly.product_bead,smul_smul,Rep.eval,Complex.ofReal_mul]
  have iden:(fun U=>(D.density x U).part s-(P.eval U:ℂ)*(Poly.pass (D.E.log x U)).part s)=Y:=by
    funext U
    have link:=WilsonMeasuredCompanionFace.on_field rent v h fit t E S w wp unit actual x s U
    change _=_+(D.density x U).part s-(O.density x U).part s at link
    rw [identity,Poly.part_smul] at link
    dsimp only [Y]
    linear_combination -link
  let rate:=(regulatorRun (C) N p f)^q
  have before(e:ℝ)(ep:0<e):Integrable Y (prior G _) ∧
      companions v w s*‖reading R (N:=N) Y u (uj.trans (by omega))‖≤(tariff*rate)*(B+e):=by
    let W:=elected v w B e
    have pos:=admitted v w wp bp ep
    have weight:0<2*(B+e):=by positivity
    have original:old.Paid W P.p.B P.p.supportExponent cash:=Hard.leasing rent
    have hard:fresh.Paid W P.p.B P.p.supportExponent (4*κ):=by
      apply Hard.mono _ (WilsonOriginalDepositedHard.paid old v h fit t W pos.1 original unit actual)
      rw [actualBudget]
      nlinarith only [mul_le_mul_of_nonneg_left small kp.le,mul_le_mul_of_nonneg_left pos.2 kp.le,kp.le]
    have paid:=sale T I N p f height fn days o D x W (route R y) center pos.1 home parent expo (regular _) hard
      cover anchor u ref uj ou oj s
    rw [iden] at paid
    refine ⟨paid.1,?_⟩
    have amount:Poly.toll W s=companions v w s*(2*(B+e))⁻¹:=by
      rw [Poly.toll,←Finset.prod_erase_mul s.val W inside]
      congr 1
      exact Finset.prod_congr rfl fun i hi=>by simp [W,elected,wage,(Finset.mem_erase.mp hi).1]
      simp [W,elected,wage]
    let normed:=‖reading R (N:=N) (p:=p) Y u (uj.trans (by omega))‖
    calc companions v w s*normed=(2*(B+e))*(Poly.toll W s*normed):=by rw [amount];field_simp
         _≤(2*(B+e))*(WilsonOriginalCompanionSpent.tariff*rate):=mul_le_mul_of_nonneg_left paid.2 weight.le
         _=(tariff*rate)*(B+e):=by unfold tariff;ring
  refine ⟨(before 1 (by norm_num)).1,?_⟩
  simpa only [mul_right_comm] using (margin (fun e ep=>(before e ep).2))
end YM.Integration.WilsonOriginalCompanionLowerPeer
end
