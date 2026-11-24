import YM.Integration.WilsonGeometricSignedClear

/-! Honest signed readings on all globally healthy nodes of the same original received post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGeometricClearPost
open FVA1 Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonPositionThermometerCapStation
open RG16.Literal Next.Rank Next.UVStress MergeProof.East OriginalForcedAddresses Exterior
open WilsonThermometerCenteredAlgebra WilsonGeometricSignedCapture
local notation "J" => Stock.census (Fin 3)
variable {G : Gauge} (R : Run G) (simple : G.Simple) {m i N per k d : ℕ}
  (cut : i<N)
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls bank φ) (hi : m ≤ i)
  (ahead : Mentor.Forecast D R.rolls bank φ books) (order shelf seats : ℕ)
variable {X : Fin 3 → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀v, Set (X v)) (pieces : ∀v, Submodule ℝ (X v)) (ages : Fin 3 → ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly J)
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead actors pieces ages
    order shelf seats i hi physical)
  (fired : Wallet actors)
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D bank π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D bank π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D bank π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "modelFee" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G (sheet).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*P.cost) (Ω⁻¹*P.rent) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) oldG
local notation "cash" => modelFee*((fig).produce (sheet).ratio.count*P.cost)
local notation "raw" => (((2:ℝ)^(order+shelf+1)/(oldG)^15)*cash)
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "βhat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "rel" => R.alloy.B.a.clock.forcedAllowance i
local notation "weights" => Stoop.radius P.w (Ω^6)

local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "configuration" => Config G (R.family.side i per)
local notation "value" => LocalComparison.actualPush R.family N per i


local notation "C" => R.family
local notation "F" => R.family.labels.level d
local notation "S" => R.family.localSection d
local notation "Y" => R.family.params
local notation "μ" => (R.family.path.levels.params i).columns
local notation "incomingAt" => LocalComparison.actualPush R.family N per i (physical fired)

local notation "debt" => (fun (ε:ℝ) (p:ℕ)=>(8*Ω^P.op.count)*P.rent+ε*g^p)
local notation "B" => ((2:ℝ)^(order+shelf+2)+4)
local notation "shine" => (fun (q:ℕ)=>βhat^(-(q:ℝ)))
local notation "M" => (fun (α:ℝ)=>WilsonFullFaceSignedPower.constants (S) (Y) α B)

include course cut in
theorem original
    (slow : ∀ j, ((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (early : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass : Pass D bank R.alloy R.kit) (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf≤R.alloy.B.a.clock.J i) (load : P.op.count≤Burn.horizon k+2)
    (p : ℕ) (deep : 2*(p+1)+8≤order) (aged : p+4≤3*k+2)
    {ε : ℝ} (positive : 0<ε) (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged positive ≤ i)
    (small : debt ε p≤1) (c : (J).Mode → ℂ) (loss q target : ℕ) (wallet K : ℝ)
    (bought : g^loss * weightBill c P.w ≤ wallet) (funded : debt ε p ≤ K*g^q)
    (surplus : target+(loss+6)≤q) :
    let nominal := fun U => Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U)
    ∀ U : configuration, flags (Ψ i).p.threshold U = ∅ →
      ‖((Ψ i).eval U:ℂ)⁻¹ * (take c (incomingAt U) - ((Ψ i).eval U:ℂ)*take c (nominal U))‖ ≤
        192*(Fintype.card (Multi.parts (J)).Mode:ℝ)*wallet*K*g^target := by
  intro nominal U clear
  let e := debt ε p
  have walk:=course.1.walk i hi cut.le
  have jj:=course.1.walk (i+1) (Nat.le_succ_of_le hi) cut
  have shape: (Ψ i).p=R.family.path.levels.budget i:=walk.truep.point
  obtain ⟨temp,beta,motion,field,div,upper,hv,room,forceRoom⟩:=
    (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose_spec i early N per cut
  have de:=P.issued.Waffle
  let ν:=(fig).produce (sheet).ratio.count*P.cost
  have c0 : 0 ≤ P.cost:=budget_nonneg (P.salary.suggests 0)
  have enough : ν ≤ 1:=calc
    _ ≤ Ω*P.cost:=mul_le_mul_of_nonneg_right de.earns c0
    _ ≤ Ω*Ω⁻¹:=mul_le_mul_of_nonneg_left P.affordable de.paysAbove.le
    _ = _:=mul_inv_cancel₀ de.paysAbove.ne'
  have wage: cash ≤ Ω:=(mul_le_of_le_one_right de.minted.le enough).trans de.quote
  have cash0 : 0≤cash:=by
    obtain ⟨_,_,_,row⟩:=(Scene.Armada.paid student P.w ages P.issued.earning (Ψ i).p de.soon).budget
    exact budget_nonneg (row ((homes) 0))
  letI : Countable P.modelIndex:=P.modelCount
  let paidWalk := (WilsonMovingMentorIncomingSlots.original R course hi cut).2.2.choose
  have band : (Ψ (i+1)).beta ∈ Shoot.band R.alloy.B.a (i+1) := by
    rw [jj.beta];exact (R.makes.wilson.represents N per (i+1) cut).band
  have allowance := Mentor.Cruise.Semester.tight D R.rolls bank R.alloy R.kit φ books pass P.op
    (Oak.era R hk D bank π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model order
    P.voter ahead jj.truep.point paidWalk walk.truep.point hospital load shelf narrow band
  have grain : Beaming.grain (R.alloy.B.a.clock.J i)≤1 := by
    unfold Beaming.grain
    exact (div_le_one (by positivity)).mpr (by linarith only [Nat.cast_nonneg (α:=ℝ) (R.alloy.B.a.clock.J i)])
  have window := (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose_spec i late
  have ceiling : Ω ≤ βhat := (allowance.1.trans (min_le_right ..)).trans
    ((Real.rpow_le_rpow_of_exponent_le (window.1.trans window.2.1) grain).trans_eq (Real.rpow_one _))
  have same : (oldG)=g:=congrArg Coat.gStep jj.beta
  have gp : 0<g:=same ▸ de.soon.1
  have low : g≤1:=same ▸ de.soon.2.1
  let x:=g⁻¹
  have x0 : 0≤x:=(inv_pos.mpr gp).le
  have tick : 1≤x:=temp
  have cap0 : cash≤2*x^2:=(wage.trans ceiling).trans beta
  have widthEq : (Ψ i).p.supportExponent+1+1=(Ψ i).p.supportExponent+2:=by ring
  have model : (lamps).Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) cash :=by
    rw [←widthEq];exact Scene.Armada.paid student P.w ages P.issued.earning (Ψ i).p de.soon
  have inc:=WilsonReceivedInheritedFee.original R hk D bank π Γ Ψ books hi cut P.op P.lesson ahead actors P.model
    P.w ages order shelf P.voter P.cost pieces P.input P.rent P.output P.issued simple p deep aged positive opened
  have old:P.output.old.Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) e:=by
    rw [←widthEq];exact P.output.old.loan_monotone P.issued.tuition inc
  have epos:0<e:=add_pos (mul_pos (mul_pos (by norm_num) (pow_pos de.paysAbove _)) P.active)
    (mul_pos positive (pow_pos gp _))
  have push : (gauge).density fired = incomingAt := (WilsonOriginalReceivedChain.report R hk D bank π Γ Ψ
    books ahead actors pieces ages order shelf seats i hi physical P fired).symm
  have paid := WilsonGeometricSignedClear.priced (lamps) P.output.old P.output.hard P.w P.issued.earning.positive
    epos.le small cash0 model old fired c U clear
  have w0 : 0 ≤ weightBill c P.w := sum_nonneg fun s _ =>
    div_nonneg (norm_nonneg _) (Poly.worth P.issued.earning.positive s).le
  have W0 := (mul_nonneg (pow_nonneg gp.le loss) w0).trans bought
  have K0 := nonneg_of_mul_nonneg_left (epos.le.trans funded) (pow_pos gp _)
  have wb : weightBill c P.w ≤ wallet/g^loss := (le_div_iff₀ (pow_pos gp _)).mpr ((mul_comm _ _).le.trans bought)
  have eb : e ≤ K*g^(target+(loss+6)) := funded.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le low surplus) K0)
  have cap : (cash+2)^3 ≤ 64/g^6 := calc
    _ ≤ (4*x^2)^3 := pow_le_pow_left₀ (by positivity) (by nlinarith only [cap0,one_le_pow₀ tick (n:=2)]) 3
    _ = _ := by dsimp only [x]; rw [div_eq_mul_inv,←inv_pow];ring
  let n : ℝ := Fintype.card (Multi.parts (J)).Mode
  have n0 : 0 ≤ n := by positivity
  rw [←push]
  calc
    _ ≤ weightBill c P.w * (3*n*e*(cash+2)^3) := paid
    _ ≤ (wallet/g^loss) * (3*n*(K*g^(target+(loss+6)))*(64/g^6)) := by gcongr
    _ = _ := by rw [pow_add, pow_add g loss];field_simp [gp.ne']; ring

end YM.Integration.WilsonGeometricClearPost
