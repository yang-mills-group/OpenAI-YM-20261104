import YM.Integration.WilsonThermometerReceivedPrior
import YM.Integration.WilsonThermometerRegisteredAncestralProperStore
import YM.Integration.WilsonThermometerRegisteredFacePair

/-! Every proper physical face can be heard on the entire older Wilson law using the same two funded signed withdrawals. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredAncestralProperPrior
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Ac OPE.Therm WilsonLimitConstruction RG16 MSbar.Heath Labels Source Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare
open scoped Classical BigOperators Topology

open MeasureTheory Exterior ConnectedActivityE6.SliceRows

open RG16.Literal Next.Rank Next.UVStress MergeProof.East OriginalForcedAddresses Exterior
open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonPositionThermometerCapStation
open WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture
open Primitives.GCC.Anchor WilsonFiniteOrdinaryInverse WilsonMeasuredCoefficientTransport
open FVA1 Function MeasureTheory Planned.GuardedAtom Extra.Histories Next.Foundations
local notation "J₃" => Stock.census (Fin 3)
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
local notation "I" => (R.family.path.levels.clock.op i per)
local notation "placed" => P.passport.coarser (I).ratio
local notation "n" => (order+shelf+2)
local notation "gs" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "stage" => R.alloy.B.a.clock.J i
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "W₀" => (Ψ i)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "roster" => Air.craft student (fun v=>(student v).paint fired) ages (π i)
  (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "lamps" => rendered student (Ψ i).p (Coat.gStep (Ψ (i+1)).beta)
open WilsonJointAxialRoster WilsonJointAxialHearing WilsonReceivedWholeFieldHot


open WilsonThermometerRegisteredAncestralProperStore WilsonThermometerRegisteredProperScale
local notation "wₚ" => (fun v=>gs*P.w v)
local notation "B" =>  (2:ℝ)^n+4
local notation "M₁" => (fun (α:ℝ)=>WilsonFullFaceSignedPower.constants (S₀) R.family.params α B)
local notation "cost₁" q:max p:max α:max => (|fee J₃*M₁ α| * (4^q+2)*gs^p)
local notation "unit₁" p:max => (|Push.Local.testPrice (F₀)*fee J₃*
    WilsonFullFaceSignedPower.inter*(Fintype.card (Multi.parts (J₃)).Mode:ℝ)*125| * gs^p)
local notation "damping" t:max => WilsonThermometerRegisteredProperScale.restoration wₚ t
local notation "book₁" t:max q:max => WilsonThermometerRegisteredProperScale.tested wₚ t q
local notation "globalFee" p:max l:max => (WilsonReceivedCloseOrdinaryGrade.invoice (J₃) (Fintype.card (Fin 3)) 0 (p+(3+l)) 1+
      (4:ℝ)^(p+(3+l)+1+2*n*(Fintype.card (Fin 3)))*(Fintype.card (Multi.parts (J₃)).Mode)*
        ((2:ℝ)^n)^(Fintype.card (Fin 3)))
local notation "modelBill" q:max p:max y:max α:max tab:max b:max =>
  Bill R A simple cut o hk D bank π Γ Ψ books hi ahead order shelf seats P q p y α tab b

def ordinate (J:Voice G) (axes:Lattice.Order) (q:ℕ) (s:(J₃).Mode) (U:Config G (R.family.side i per)):ℂ:=
  let H := radius R (invoice (Fintype.card (Fin 3)) (q+2*n)) 1 i
  let r := amplitude R J H N per i
  let τ := angularCut (R.family.path.levels.clock.hatBeta i)
  let k₀ := (WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
  let cold := House.chilly (G:=G) (plaquettes (placed).origin H) τ
  let angle := WilsonJointAxialHearing.angleOf (placed).origin k₀ J axes r gs
  cold.indicator (fun V=>WilsonCoveredOrdinaryPolynomial.evaluated order
    (fun d=>Air.discharge roster d (angle V)) (gs:ℂ) s) U

local notation "scalar" J:max axes:max q:max s:max U:max => ordinate R A simple cut o hk D bank π Γ Ψ books hi ahead order shelf seats
  P J axes q s U
def covered (J:Voice G) (axes:Lattice.Order) (q:ℕ) (U:Config G (R.family.side i per)):Poly (J₃):=
  Poly.inject fun s=>scalar J axes q s U

local notation "published" J:max axes:max q:max U:max => covered R A simple cut o hk D bank π Γ Ψ books hi ahead order shelf seats
  P J axes q U

theorem value (J:Voice G) (axes:Lattice.Order) (q:ℕ) (U:Config G (R.family.side i per)) (tab:Poly J₃):
    (total (published J axes q U) tab).part full=∑s,WilsonThermometerCenteredAlgebra.weight tab s*scalar J axes q s U:=by
  rw [WilsonThermometerCenteredAlgebra.affine];rfl

def signed (J:Voice G) (axes:Lattice.Order) (q:ℕ) (Q:Poly (J₃)) (t:(J₃).Mode)
    (b h:Coefficient F₀ (R.family.side i per)) (U:Config G (R.family.side i per)):ℂ:=
  (total (incoming R A simple cut.le o U) Q).part (complement t)/((Ψ i).eval U:ℂ)-
    (total (published J axes q U) Q).part (complement t)-
    ((damping t):ℂ)*(account h (Ψ i) U-account b (Ψ i) U)/((Ψ i).eval U:ℂ)

include course cut in
theorem original {η : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (funded : FundedOriginalProperties.{u} simple η W)
    (slow : ∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J : Voice G) (clear : Clear G J) (axes : Lattice.Order) (q : ℕ) {ε : ℝ} (ep : 0 < ε)
    (width : ∀ j k : ℕ, k ≤ j → ∀ b : ℝ, R.alloy.delay.betaEntry j ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) j)⁻¹ ^ 2) ≤ b)
    (law : VowsR.LawScroll G φ) (enrolled : VowsR.Chamber law R.kit D bank books)
    (fund : Volume.Fund D R.rolls bank φ books R.alloy.delay)
    (late : max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card (Fin 3)) n q ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width order shelf (Fintype.card (Fin 3)) ep) ≤ i)
    (finiteLate : max (WilsonReceivedAxialFinite.opening R simple q ep)
      (WilsonReceivedAxialFinite.massOpening R D ages order shelf seats (k:=k) simple width) ≤ i)
    (pass : Pass D bank R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) (fit : k ≤ stage)
    (gate : WilsonReportingForestAngularReflection.posted R) (p l : ℕ)
    (reserve : p+(3+l)+1+Fintype.card (Fin 3) ≤ q) (headroom : q ≤ order)
    (accuracy : ε*((3:ℝ)^q+2) ≤ 1)
    (clockLate : (eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose ≤ i)
    (rareLate : WilsonJointAxialScalar.opening (V:=Fin 3) R simple gate q n (p+(3+l)+1+2*n*(Fintype.card (Fin 3))) ≤ i)
    (winding : (eventually_atTop.mp (WilsonCoveredOrdinaryWeightedPost.original R simple D φ ages
      width order shelf k seats 0 (Fintype.card (Fin 3)) (3+l) (p+1) 1 1 (fee (J₃)) zero_le_one ep)).choose ≤ i)
    (aperture : gs^l ≤ Poly.toll P.w full) (Q₀ : Poly (J₃))
    (inverse : Poly.price (fun v=>gs*P.w v) (inverseMass Q₀)≤fee (J₃))

    (y:Site (R.family.side i per)) (α:ℝ) (t:(J₃).Mode) (live:t≠(J₃).quiet)
    (appointed:Filed R A simple cut o hk D bank π Γ Ψ books hi ahead order shelf seats P q (p+1) y α Q₀ t):
    ∃b h:Coefficient F₀ (R.family.side i per),
      (modelBill q (p+1) y α 1 b) ∧ (modelBill q (p+1) y α (book₁ t Q₀) h) ∧
      let err:=signed R A simple cut o hk D bank π Γ Ψ books hi ahead order shelf seats P J axes q Q₀ t b h
      RG.Envelope err ∧ ∀ j (age:j ≤ i),
      (∫U,‖actualTransport R.family (N:=N) err age U‖ ∂scene R.family.path N per j)≤
        damping t*(2*((fee (J₃)*globalFee p l+ε)*gs^(p+1)+(unit₁ (p+1)+cost₁ q (p+1) α))):=by
  obtain ⟨b,h,blank,tinted,submission⟩:=appointed
  refine ⟨b,h,blank,tinted,?_⟩
  dsimp only
  let src := fun U=>incoming R A simple cut.le o U
  let pay := fun (tab:Poly J₃) (n₀:Coefficient F₀ (R.family.side i per)) U=>
    (total (src U) tab).part full/((Ψ i).eval U:ℂ)-
      (∑s,WilsonThermometerCenteredAlgebra.weight tab s*scalar J axes q s U)-account n₀ (Ψ i) U/((Ψ i).eval U:ℂ)
  let fare:=(fee (J₃)*globalFee p l+ε)*gs^(p+1)+(unit₁ (p+1)+cost₁ q (p+1) α)
  have beta:=congrArg Coat.gStep (course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).beta
  have pos:0<gs:=beta ▸ P.issued.Waffle.soon.1
  have widths(v):0<(wₚ) v:=mul_pos pos (P.salary.positive v)
  have earned:=WilsonThermometerRegisteredProperScale.fixed wₚ t widths live Q₀ inverse
  have hearing (tab:Poly J₃) (n₀:Coefficient F₀ (R.family.side i per))
      (affordable:Poly.price wₚ (inverseMass tab)≤fee J₃)
      (row:modelBill q (p+1) y α tab n₀):
      RG.Envelope (pay tab n₀) ∧ (∫U,‖pay tab n₀ U‖ ∂scene R.family.path N per i)≤fare:=by
    have issued:=WilsonThermometerReceivedPrior.original R A simple cut o hk D bank π Γ Ψ course books hi ahead order shelf seats
      P funded slow J clear axes q ep width law enrolled fund late finiteLate pass hospital narrow load fit gate p l reserve headroom
      accuracy clockLate rareLate winding aperture tab affordable y n₀ row.1 row.2.1 row.2.2.1
    have unit:‖n₀.x 0‖ ≤ unit₁ (p+1):=
      (Finset.single_le_sum (fun j _=>norm_nonneg (n₀.x j)) (Finset.mem_univ 0)).trans row.2.2.2
    have baseCost:=issued.2 i le_rfl
    simp only [actualTransport_base R.family R.makes cut.le] at baseCost
    have paidAt:(∫U,‖pay tab n₀ U‖ ∂scene R.family.path N per i)≤
        (fee (J₃)*globalFee p l+ε)*gs^(p+1)+(‖n₀.x 0‖+cost₁ q (p+1) α):=baseCost
    exact ⟨issued.1,paidAt.trans (add_le_add le_rfl (add_le_add unit le_rfl))⟩
  have lower:=hearing 1 b earned.1 blank
  have upper:=hearing (book₁ t Q₀) h earned.2 tinted
  have identity:signed R A simple cut o hk D bank π Γ Ψ books hi ahead order shelf seats P J axes q Q₀ t b h=
      fun U=>(damping t:ℂ)*((pay (book₁ t Q₀) h) U-(pay 1 b) U):=by
    funext U
    unfold signed
    dsimp only [pay,src]
    rw [WilsonThermometerRegisteredProperScale.ordinary wₚ t widths (src U) Q₀ live,
        WilsonThermometerRegisteredProperScale.ordinary wₚ t widths (published J axes q U) Q₀ live,
        value R A simple cut o hk D bank π Γ Ψ books hi ahead order shelf seats P J axes q U (book₁ t Q₀),
        value R A simple cut o hk D bank π Γ Ψ books hi ahead order shelf seats P J axes q U 1]
    ring
  rw [identity]
  have outcome:=WilsonThermometerRegisteredFacePair.difference R cut.le _ _ upper.1 lower.1 fare upper.2 lower.2 ((damping t):ℂ)
  have good:=WilsonThermometerRegisteredProperScale.positive wₚ t widths
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos good] using outcome

end YM.Integration.WilsonThermometerRegisteredAncestralProperPrior
