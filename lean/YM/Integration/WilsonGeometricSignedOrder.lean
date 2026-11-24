import YM.Integration.WilsonThermometerFullSignedOrder
import YM.Integration.WilsonGeometricSignedPower

/-! Spend one externally issued face wallet before hearing the signed physical capture. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGeometricSignedOrder
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
private theorem spend (c : ℝ) {g a W C K : ℝ} {loss l q target : ℕ}
    (gp : 0 < g) (low : g ≤ 1) (w0 : 0 ≤ W) (bill : g^loss*W ≤ C)
    (a0 : 0 ≤ a) (paid : a ≤ K*g^q) (surplus : target+(loss+l)≤q) :
    W*(c*(g⁻¹)^l*a) ≤ |c| *C*K*g^target := by
  have C0 := (mul_nonneg (pow_nonneg gp.le loss) w0).trans bill
  have K0 := nonneg_of_mul_nonneg_left (a0.trans paid) (pow_pos gp _)
  have wle : W ≤ C/g^loss := (le_div_iff₀ (pow_pos gp _)).mpr ((mul_comm _ _).le.trans bill)
  calc
    _ ≤ W*(|c| *(g⁻¹)^l*a) := by gcongr; exact le_abs_self _
    _ ≤ (C/g^loss)*(|c| *(g⁻¹)^l*(K*g^(target+(loss+l)))) := by
      apply mul_le_mul wle _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left
        (paid.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le low surplus) K0)) (by positivity)
    _ = _ := by rw [pow_add, pow_add g loss, inv_pow]; field_simp [gp.ne']

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
theorem original (gradeCap : (∑j,ages j) ≤ 14) (way : WayStation R.kit) (station : WilsonCenteredCaptureClock.first R simple ≤ i)
    (sec : R.t d ≤ i)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (early : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass : Pass D bank R.alloy R.kit) (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf≤R.alloy.B.a.clock.J i) (load : P.op.count≤Burn.horizon k+2)
    (p q : ℕ) (force : q≤R.alloy.B.a.clock.J i) (deep : 2*(p+1)+8≤order) (aged : p+4≤3*k+2)
    {ε : ℝ} (positive : 0<ε) (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged positive ≤ i)
    (small : debt ε p≤1) (c : (J).Mode → ℂ) (y : Site ((C).side i per)) (Z : Support ((C).side i per)) (center : y∈Z)
    (homes_in : ∀j:Fin 3,homes j∈Z) (rad : ℕ) (near : ∀j:Fin 3,separation (homes j) y≤rad)
    (radius : rad≤(Ψ i).p.B) (box : Z⊆halo (Ψ i).p.B {y}) (α : ℝ) (strength : (Ψ i).p.supportExponent≤α)
    (loss : ℕ) (wallet K : ℝ) (bought : g^loss * weightBill c P.w ≤ wallet)
    (target : ℕ) (surplus : target+(loss+87)≤q) (funded : debt ε p ≤ K*g^q)
    (saved : (eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose ≤ i) :
    let nominal := fun U=>Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U)
    ∃ h : Coefficient (F) ((C).side i per),h.Format y (Y) (Ψ i) ∧
      h.remBound y (Ψ i) κ (|M α| * wallet * (K+4^q+1) * g^target) ∧
      (∀U,h.density y (S) (Ψ i) U=take c (incomingAt U)-
        ((Ψ i).eval U:ℂ)*take c (nominal U)) ∧
      let scalar := ((Ψ i).eval (1:configuration):ℂ)⁻¹ * (take c (incomingAt 1) -
        ((Ψ i).eval (1:configuration):ℂ)*take c (nominal 1))
      (∀ a : Probe G d, a.2.val=0 → runProbe (F) a h.x = scalar) ∧
      ‖scalar‖ ≤ |WilsonFullFaceSignedPower.inter * (Fintype.card (Multi.parts (J)).Mode:ℝ)*125| *
        wallet * K * g^target := by
  intro nominal
  obtain ⟨h,fmt,rem,answer,unit,size⟩ := WilsonGeometricSignedPower.stored R simple cut hk D bank π Γ Ψ
    course books hi ahead order shelf seats actors pieces ages physical P fired gradeCap way station sec slow
    ready early late pass hospital narrow load p q force deep aged positive opened small c y Z center
    homes_in rad near radius box α strength
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
  have funding : debt ε p+shine q+hitWidth (Ψ i).p*rel/κ ≤ (K+4^q+1)*g^q := by
    linarith only [funded,reserve]
  have weight0 : 0 ≤ weightBill c P.w := Finset.sum_nonneg fun s _ =>
    div_nonneg (norm_nonneg _) (Poly.worth P.issued.earning.positive s).le
  have money := spend (M α) g0 low weight0 bought
    (show 0 ≤ debt ε p+shine q+hitWidth (Ψ i).p*rel/κ by rw [add_assoc]; exact add_nonneg paid rn)
    funding surplus
  let k0 := WilsonFullFaceSignedPower.inter * (Fintype.card (Multi.parts (J)).Mode:ℝ)*125
  have primary := spend k0 g0 low weight0 bought paid funded (l:=6) (target:=target) (by omega)
  obtain ⟨a,b,forced,factor,toll,wit⟩ := rem
  refine ⟨h,fmt,⟨a,b,forced,factor,toll.trans money,wit⟩,answer,unit,size.trans ?_⟩
  calc
    _ = weightBill c P.w * (k0*(g⁻¹)^6*(debt ε p)) := by
      dsimp only [k0]
      rw [div_eq_mul_inv,←inv_pow]
      ring
    _ ≤ _ := primary

end YM.Integration.WilsonGeometricSignedOrder
