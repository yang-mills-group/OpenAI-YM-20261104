import YM.Integration.WilsonThermometerFullSignedPower
import YM.Integration.WilsonFullFaceSignedReserved

/-! The full signed three-name capture at its requested accuracy on the funded original post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFullSignedOrder
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
private theorem settle (cst:ℝ) {g a K:ℝ} {d q target:ℕ}
    (gp:0<g) (low:g≤1) (surplus:target+d≤q) (p0:0≤a) (paid:a≤K*g^q) :
    cst/g^d*a ≤ |cst| * K*g^target:=by
  have nonneg:0≤K:=nonneg_of_mul_nonneg_left (p0.trans paid) (pow_pos gp q)
  calc
    _ = cst*a/g^d:=by ring
    _ ≤ |cst| * (K*g^q)/g^d:=div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_right (le_abs_self _) p0).trans
       (mul_le_mul_of_nonneg_left paid (abs_nonneg _))) (pow_nonneg gp.le _)
    _ ≤ |cst| * (K*g^(target+d))/g^d:=div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one gp.le low surplus) nonneg) (abs_nonneg _)) (pow_nonneg gp.le _)
    _ = _:=by rw [pow_add];field_simp

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
    (inverse : Poly.price (fun v=>g*P.w v) (inverseMass Q)≤fee J) 
    (target:ℕ) (surplus:target+(3+loss+87)≤q) (funded:debt ε p≤g^q)
    (saved:(eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose ≤ i) :
    let nominal := fun U=>Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U)
    ∃ h : Coefficient (F) ((C).side i per), h.Format y (Y) (Ψ i) ∧
      h.remBound y (Ψ i) κ (|fee J*M α| * (4^q+2)*g^target) ∧
      (∀U:configuration,h.density y (S) (Ψ i) U=(total (incomingAt U) Q).part full-
        ((Ψ i).eval U:ℂ)*(total (nominal U) Q).part full) ∧
      (F).coeffSize h.x ≤ |testPrice (F)*fee J*WilsonFullFaceSignedPower.inter*
        (Fintype.card (Multi.parts (J)).Mode:ℝ)*125| * g^target :=by
  intro nominal
  obtain ⟨h,fmt,rem,answer,_,size⟩:=WilsonThermometerFullSignedPower.stored R A simple cut o hk D bank π Γ Ψ course books hi ahead
    order shelf seats P way station sec slow ready early late pass hospital narrow load p q force deep aged positive opened
    small Q y Z center homes_in rad near radius box α strength loss aperture inverse
  have w:=course.1.walk i hi cut.le
  have head:=course.1.walk (i+1) (Nat.le_succ_of_le hi) cut
  have g0:0<g:=(congrArg Coat.gStep head.beta) ▸ P.issued.Waffle.soon.1
  have low:g≤1:=(congrArg Coat.gStep head.beta) ▸ P.issued.Waffle.soon.2.1
  have shape : (Ψ i).p=R.family.path.levels.budget i:=w.truep.point
  have reserve:shine q+hitWidth (Ψ i).p*rel/κ ≤ (4^q+1)*g^q :=by
    rw [shape];exact (eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose_spec i saved N per cut
  have paid:0≤debt ε p:=add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (pow_nonneg P.issued.Waffle.paysAbove.le _)) P.active.le) (mul_nonneg positive.le (pow_nonneg g0.le _))
  have H0:0<βhat:=zero_lt_one.trans (R.family.path.levels.fits.delayed (i+1))
  have shape0:0≤hitWidth (Ψ i).p:=by unfold hitWidth;positivity
  have rel0:=allowance_pos R.family.path.levels.clock i
  have κ0:0<κ:=Real.sqrt_pos.mpr rel0
  have rn:0 ≤ shine q+hitWidth (Ψ i).p*rel/κ:=add_nonneg (Real.rpow_pos_of_pos H0 _).le
    (div_nonneg (mul_nonneg shape0 rel0.le) κ0.le)
  have funding:debt ε p+shine q+hitWidth (Ψ i).p*rel/κ ≤ (4^q+2)*g^q:=by
    linarith only [funded,reserve]
  have money:=settle (fee J*M α) g0 low surplus (show 0≤debt ε p+shine q+hitWidth (Ψ i).p*rel/κ by
    rw [add_assoc];exact add_nonneg paid rn) funding
  have primary:=settle (testPrice (F)*fee J*WilsonFullFaceSignedPower.inter*(Fintype.card (Multi.parts (J)).Mode:ℝ)*125)
    g0 low (show target+(3+loss+6)≤q by omega) paid (K:=1) (funded.trans_eq ((one_mul _).symm))
  obtain ⟨a,b,c,d,toll,wit⟩:=rem
  exact ⟨h,fmt,⟨a,b,c,d,toll.trans money,wit⟩,answer,by simpa only [mul_one] using size.trans primary⟩

end YM.Integration.WilsonThermometerFullSignedOrder
