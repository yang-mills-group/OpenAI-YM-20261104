import YM.Integration.WilsonFullFaceSignedPower
import YM.Integration.WilsonFullFacePooledUnit
import YM.Integration.WilsonThermometerOrdinaryHalo
import YM.Integration.WilsonThermometerPlantedScalar

/-! The same signed original post at the physical source radii. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFullSignedPower
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
open WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture
open Primitives.GCC.Anchor WilsonFiniteOrdinaryInverse
local notation "J" => Stock.census (Fin 3)
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {m i N per k : ℕ}
  (cut : i<N) (o : Positions (Fin 3) (R.family.side N per))
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls bank φ) (hi : m ≤ i)
  (ahead : Mentor.Forecast D R.rolls bank φ books) (order shelf seats : ℕ)
local notation "ages" => (fun j:Fin 3=>(WilsonPositionThermometerGradedSource.grade j).val)
local notation "actual" => offered R A simple cut o
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead disks sectors ages
  order shelf seats i hi (offered R A simple cut o))
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D bank π Γ books hi P.op P.lesson ahead disks
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
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params
local notation "μ" => (R.family.path.levels.params i).columns
local notation "incomingAt" => incoming R A simple cut.le o

local notation "debt" => (fun (ε:ℝ) (p:ℕ)=>(8*Ω^P.op.count)*P.rent+ε*g^p)
local notation "B" => ((2:ℝ)^(order+shelf+2)+4)
local notation "shine" => (fun (q:ℕ)=>βhat^(-(q:ℝ)))
local notation "M" => (fun (α:ℝ)=>WilsonFullFaceSignedPower.constants (S) (Y) α B)

include course cut in
theorem stored (way : WayStation R.kit) (station : WilsonCenteredCaptureClock.first R simple ≤ i)
    (sec : R.t 0 ≤ i)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (early : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass : Pass D bank R.alloy R.kit) (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf≤R.alloy.B.a.clock.J i) (load : P.op.count≤Burn.horizon k+2)
    (p q : ℕ) (force : q≤R.alloy.B.a.clock.J i) (deep : 2*(p+1)+8≤order) (aged : p+4≤3*k+2)
    {ε : ℝ} (positive : 0<ε) (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged positive ≤ i)
    (small : debt ε p≤1) (Q : Poly J) (y : Site ((C).side i per)) (Z : Support ((C).side i per)) (center : y∈Z)
    (homes_in : ∀j:Fin 3,homes j∈Z) (rad : ℕ) (near : ∀j:Fin 3,separation (homes j) y≤rad)
    (radius : rad≤(Ψ i).p.B) (box : Z⊆halo (Ψ i).p.B {y}) (α : ℝ) (strength : (Ψ i).p.supportExponent≤α)
    (loss : ℕ) (aperture : g^loss≤Poly.toll P.w full)
    (inverse : Poly.price (fun v=>g*P.w v) (inverseMass Q)≤fee J) :
    let nominal := fun U=>Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U)
    let cost := debt ε p+shine q+hitWidth (Ψ i).p*rel/κ
    ∃ h : Coefficient (F) ((C).side i per),h.Format y (Y) (Ψ i) ∧
      h.remBound y (Ψ i) κ ((fee (J)*M α)/g^(3+loss+87)*cost) ∧
      (∀U,h.density y (S) (Ψ i) U=(total (incomingAt U) Q).part full-
        ((Ψ i).eval U:ℂ)*(total (nominal U) Q).part full) ∧
      (F).coeffSize h.x ≤ testPrice (F)*‖((Ψ i).eval (1:configuration):ℂ)⁻¹*
        ((total (incomingAt 1) Q).part full-((Ψ i).eval (1:configuration):ℂ)*(total (nominal 1) Q).part full)‖ ∧
      (F).coeffSize h.x ≤ (testPrice (F)*fee (J)*WilsonFullFaceSignedPower.inter*
        (Fintype.card (Multi.parts (J)).Mode:ℝ)*125)/g^(3+loss+6)*(debt ε p) :=by
  intro nominal cost
  have walk:=course.1.walk i hi cut.le
  have jj:=course.1.walk (i+1) (Nat.le_succ_of_le hi) cut
  have shape: (Ψ i).p=R.family.path.levels.budget i:=walk.truep.point
  have read :=(WilsonCapturedPrimarySection.original R sec (Ψ i) shape).1
  obtain ⟨temp,beta,motion,field,div,upper,hv,room,forceRoom⟩:=
    (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose_spec i early N per cut
  obtain ⟨h,fmt,account,answer,unit⟩:=WilsonThermometerFullSignedRent.paidAt R A simple cut o hk D bank π Γ Ψ course books hi ahead order shelf seats P way station μ read p q force deep aged positive opened Q y Z center homes_in rad near
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
  have wallet := Mentor.Cruise.Semester.tight D R.rolls bank R.alloy R.kit φ books pass P.op
    (Oak.era R hk D bank π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model order
    P.voter ahead jj.truep.point paidWalk walk.truep.point hospital load shelf narrow band
  have grain : Beaming.grain (R.alloy.B.a.clock.J i)≤1 := by
    unfold Beaming.grain
    exact (div_le_one (by positivity)).mpr (by linarith only [Nat.cast_nonneg (α:=ℝ) (R.alloy.B.a.clock.J i)])
  have window := (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose_spec i late
  have ceiling : Ω ≤ βhat := (wallet.1.trans (min_le_right ..)).trans
    ((Real.rpow_le_rpow_of_exponent_le (window.1.trans window.2.1) grain).trans_eq (Real.rpow_one _))
  have same : (oldG)=g:=congrArg Coat.gStep jj.beta
  have gp : 0<g:=same ▸ de.soon.1
  have low : g≤1:=same ▸ de.soon.2.1
  let x:=g⁻¹
  have x0 : 0≤x:=(inv_pos.mpr gp).le
  have tick : 1≤x:=temp
  have cap0 : cash≤2*x^2:=(wage.trans ceiling).trans beta
  have fine : (2:ℝ)^(order+shelf+2) ≤ B :=by linarith
  have x2 : x^2≤x^17:=pow_le_pow_right₀ tick (by norm_num)
  have whole : 1≤x^17:=one_le_pow₀ tick
  have b1 : 1≤B:=by
    have t:0≤(2:ℝ)^(order+shelf+2):=by positivity
    linarith only [t]
  have cplus : cash+3≤B*x^17 :=by
    have base : (2:ℝ)≤2^(order+shelf+2):=by
      simpa using (pow_le_pow_right₀ (show (1:ℝ)≤2 by norm_num) (show 1≤order+shelf+2 by omega))
    nlinarith only [cap0, x2, whole,mul_nonneg (sub_nonneg.mpr base) (pow_nonneg x0 17)]
  have raw0 : 0≤raw:=mul_nonneg (div_nonneg (by positivity) (pow_nonneg de.soon.1.le _)) cash0
  have rawCap : raw≤B*x^17 :=by
    rw [same,div_eq_mul_inv,←inv_pow]
    change (2:ℝ)^(order+shelf+1)*x^15*cash≤_
    calc _ ≤ 2^(order+shelf+1)*x^15*(2*x^2):=mul_le_mul_of_nonneg_left cap0 (by positivity)
         _ = 2^(order+shelf+2)*x^17:=by rw [show order+shelf+2=order+shelf+1+1 by omega,pow_succ];ring
         _ ≤ _:=mul_le_mul_of_nonneg_right fine (pow_nonneg x0 _)
  let e:=debt ε p
  have e0 : 0≤e:=add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg de.paysAbove.le _)) P.active.le)
    (mul_nonneg positive.le (pow_nonneg gp.le _))
  have shrink:=one_le_pow₀ de.cool (n:=6)
  have radiusCap : Ω^6≤64*x^12:=calc
    _ ≤ (2*x^2)^6:=pow_le_pow_left₀ de.paysAbove.le (ceiling.trans beta) _
    _ = _:=by ring
  have e0' : 0≤(Ω^6)⁻¹*(cash+e):=mul_nonneg (inv_nonneg.mpr (zero_le_one.trans shrink)) (add_nonneg cash0 e0)
  have ec : (Ω^6)⁻¹*(cash+e)≤B*x^17:=
    (mul_le_of_le_one_left (add_nonneg cash0 e0) (inv_le_one_of_one_le₀ shrink)).trans
      ((by linarith only [show e≤1 from small] : cash+e≤cash+3).trans cplus)
  have bp : 1≤βhat:=(R.alloy.B.a.fits.delayed (i+1)).le
  have rare0 : 0 ≤ shine q:=Real.rpow_nonneg (zero_le_one.trans bp) _
  have rare1 : shine q≤1:=Real.rpow_le_one_of_one_le_of_nonpos bp (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hard0 := mul_nonneg rare0 div.le
  have hard1 : (shine q)*κ≤1:=(mul_le_of_le_one_left div.le rare1).trans upper
  have paid : shine q*κ/κ=shine q:=mul_div_cancel_right₀ _ div.ne'
  let fare (s:(J).Mode):=WilsonFullFaceSignedCapture.fare (Ψ i).p (S) (Y) Z P.w weights s rad cash e raw
    (shine q*κ) ((Ω^6)⁻¹*(cash+e)) rel κ μ
  have perFace (s:(J).Mode) : Poly.toll P.w s*fare s≤M α*x^87*cost:=by
    dsimp only [fare]
    rw [show weights=(fun j=>P.w j/Ω^6) from rfl]
    simpa only [cost,e,paid] using WilsonFullFaceSignedPower.face (Ψ i).p (S) (Y) P.w P.issued.earning.positive s y Z box rad radius strength b1 tick cash0 raw0 e0 small e0' cplus rawCap ec shrink radiusCap hard0 hard1 div hv (shape ▸ room) (shape ▸ forceRoom) (shape ▸ motion) (zero_le_one.trans (R.family.path.levels.params i).columns_ge) field
  have m0 : 0≤M α:=by
    unfold WilsonFullFaceSignedPower.constants WilsonPlantedOrdinaryHalo.master WilsonFullFaceSignedHalo.roof
    have b0:=zero_le_one.trans b1
    have ip:0 ≤ WilsonFullFaceSignedPower.inter:=WilsonFullFaceSignedPower.bounded.choose_spec.1
    positivity
  have cost0:0≤cost:=add_nonneg (add_nonneg e0 rare0) (div_nonneg (mul_nonneg (by unfold hitWidth;positivity) hv) div.le)
  have invoice := WilsonThermometerCenteredWeight.original Q P.w P.issued.earning.positive gp low loss aperture inverse
  have totalPrice : (∑s:(J).Mode, ‖weight Q s‖/Poly.toll P.w s)≤(fee J)/g^(3+loss) :=
    (le_div_iff₀ (pow_pos gp _)).mpr (by simpa only [mul_comm] using invoice)
  have bill : (∑s:(J).Mode,‖weight Q s‖*fare s)≤((fee J)*M α)/g^(3+loss+87)*cost :=calc
    _ ≤ ∑s:(J).Mode,(‖weight Q s‖/Poly.toll P.w s)*(M α*x^87*cost) :=sum_le_sum fun s _=>
      (mul_le_mul_of_nonneg_left ((le_div_iff₀ (Poly.worth P.issued.earning.positive s)).mpr
        ((mul_comm (fare s) (Poly.toll P.w s)).le.trans (perFace s))) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := (Finset.sum_mul ..).symm
    _ ≤ (fee J/g^(3+loss))*(M α*x^87*cost) :=mul_le_mul_of_nonneg_right totalPrice (by positivity)
    _ = _ := by dsimp only [x];rw [pow_add];ring
  obtain ⟨a,b,c,d,price,wit⟩:=account
  have widthEq : (Ψ i).p.supportExponent+1+1=(Ψ i).p.supportExponent+2:=by ring
  have model : (lamps).Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) cash :=by
    rw [←widthEq];exact Scene.Armada.paid student P.w ages P.issued.earning (Ψ i).p de.soon
  have inc:=WilsonReceivedInheritedFee.original R hk D bank π Γ Ψ books hi cut P.op P.lesson ahead disks P.model
    P.w ages order shelf P.voter P.cost sectors P.input P.rent P.output P.issued simple p deep aged positive opened
  have old:P.output.old.Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) e:=by
    rw [←widthEq];exact P.output.old.loan_monotone P.issued.tuition inc
  have epos:0<e:=add_pos (mul_pos (mul_pos (by norm_num) (pow_pos de.paysAbove _)) P.active)
    (mul_pos positive (pow_pos gp _))
  have frame := WilsonFullFacePooledUnit.price (lamps) P.output.old P.output.hard P.w P.issued.earning.positive
    epos small cash0 model old fired Q gp low loss aperture inverse
  have push : (gauge).density fired = incomingAt :=by
    rw [←WilsonOriginalReceivedChain.report R hk D bank π Γ Ψ books ahead disks sectors ages
      order shelf seats i hi actual P fired,fired_input,WilsonThermometerCourseIntake.step]
  let count : ℝ:=Fintype.card (Multi.parts (J)).Mode
  let inter:=WilsonFullFaceSignedPower.inter
  have answerUnit : ‖((Ψ i).eval (1:configuration):ℂ)⁻¹*
      ((total (incomingAt 1) Q).part full-((Ψ i).eval (1:configuration):ℂ)*(total (nominal 1) Q).part full)‖ ≤
      fee J/g^(3+loss)*(e*inter*(count*(cash+3)^3)):=by
    rw [←push];exact frame
  have t0:0≤testPrice (F):=zero_le_one.trans (probe_budget (F)).choose_spec.choose_spec.1
  exact ⟨h,fmt,⟨a,b,c,d,price.trans bill,wit⟩,answer,unit,
    (unit.trans (mul_le_mul_of_nonneg_left answerUnit t0)).trans
      (WilsonFullFacePooledUnit.projected (testPrice (F)) g cash e loss t0 gp low e0 cash0 cap0)⟩

include course cut in
theorem original (way : WayStation R.kit) (station : WilsonCenteredCaptureClock.first R simple ≤ i)
    (sec : R.t 0 ≤ i)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (early : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass : Pass D bank R.alloy R.kit) (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf≤R.alloy.B.a.clock.J i) (load : P.op.count≤Burn.horizon k+2)
    (p q : ℕ) (force : q≤R.alloy.B.a.clock.J i) (deep : 2*(p+1)+8≤order) (aged : p+4≤3*k+2)
    {ε : ℝ} (positive : 0<ε) (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged positive ≤ i)
    (small : debt ε p≤1) (Q : Poly J) (y : Site ((C).side i per)) (Z : Support ((C).side i per)) (center : y∈Z)
    (homes_in : ∀j:Fin 3,homes j∈Z) (rad : ℕ) (near : ∀j:Fin 3,separation (homes j) y≤rad)
    (radius : rad≤(Ψ i).p.B) (box : Z⊆halo (Ψ i).p.B {y}) (α : ℝ) (strength : (Ψ i).p.supportExponent≤α)
    (loss : ℕ) (aperture : g^loss≤Poly.toll P.w full)
    (inverse : Poly.price (fun v=>g*P.w v) (inverseMass Q)≤fee J) :
    let nominal := fun U=>Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U)
    let cost := debt ε p+shine q+hitWidth (Ψ i).p*rel/κ
    ∃ h : Coefficient (F) ((C).side i per),h.Format y (Y) (Ψ i) ∧
      h.remBound y (Ψ i) κ ((fee (J)*M α)/g^(3+loss+87)*cost) ∧
      (∀U,h.density y (S) (Ψ i) U=(total (incomingAt U) Q).part full-
        ((Ψ i).eval U:ℂ)*(total (nominal U) Q).part full) ∧
      (F).coeffSize h.x ≤ testPrice (F)*‖((Ψ i).eval (1:configuration):ℂ)⁻¹*
        ((total (incomingAt 1) Q).part full-((Ψ i).eval (1:configuration):ℂ)*(total (nominal 1) Q).part full)‖ := by
  intro nominal cost
  obtain ⟨h,format,paid,issued,unit,-⟩:=stored R A simple cut o hk D bank π Γ Ψ course books hi ahead order shelf seats P
    way station sec slow ready early late pass hospital narrow load p q force deep aged positive opened small Q y Z center homes_in rad near radius box α strength loss aperture inverse
  exact ⟨h,format,paid,issued,unit⟩

end YM.Integration.WilsonThermometerFullSignedPower
