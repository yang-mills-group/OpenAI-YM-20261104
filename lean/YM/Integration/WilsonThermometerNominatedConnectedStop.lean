import YM.Integration.WilsonThermometerRegisteredCenteredConnectedTest
import YM.Integration.WilsonThermometerRegisteredCenteredStore
import YM.Integration.WilsonThermometerReflectedTwoBills
/-! The nominated connected scalar on the full physical reflected Wilson source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerNominatedConnectedStop
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

local notation "strip" => (∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
  Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
local notation "roster" => Air.craft P.model (fun v=>(P.model v).paint fired) ages
  (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "base" => Stationary.arm G (R.family.side i per) 1
local notation "program" => (RunFormalChain.fromRun R).step N i per cut


open Function Set Filter Finset Marker Extra.Trajectories Primitives.GCC.Anchor
open Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch FormalBulk08 FormalBulk08.Flat
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Soil WilsonCoeffUV.Shard WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider PhysicalNext.Repeat.Legato Labels Source Next.Foundations
open WilsonConditionalTaylorWheelConnectedReadout WilsonThermometerCenteredAlgebra
open Extraction Table Spec Climb Trace.Pilot Next.UVStress Next.Rank RG12 RG17 PhysMS
open XSpace XSpace.Normalize XSpace.Rose WilsonPositionThermometerCapStation
open WilsonThermometerRegisteredAncestralProperStore
local notation "wₚ" => (fun v=>g*P.w v)
local notation "submitted₀" U:max => (Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U))
local notation "damping" t:max Q:max => WilsonThermometerRegisteredRestrictedWithdrawal.restoration wₚ t Q
local notation "book₁" t:max Q:max => WilsonThermometerRegisteredRestrictedWithdrawal.tested wₚ t Q
local notation "cost₁" q:max target:max α:max => (|fee J*M α| * (4^q+2)*g^target)
local notation "units" target:max => (|testPrice (F)*fee J*WilsonFullFaceSignedPower.inter*
        (Fintype.card (Multi.parts (J)).Mode:ℝ)*125| * g^target)

open OPE.Cards WilsonThermometerNominatedFaceCylinder WilsonThermometerAlignedCells WilsonThermometerFiniteConnectedCells
local notation "UV" => ((N,per):UVIndex)
local notation "Fₓ" s:max => WilsonThermometerCourseIntake.placed R A UV (s).val o.origin
local notation "Z" => Cut R.family N per
local notation "paidStore" => WilsonThermometerRegisteredCenteredStore.Charged R A simple cut o hk D bank π Γ Ψ books hi ahead order shelf seats P
local notation "stamp" => WilsonThermometerUnitFilingFeed.report R
local notation "paid" fee:max s:max u:max j:max => PaidAt R.family.S N per j (R.family.beta N per) (fee s)
  ((Fₓ s)-stamp (Fₓ s) u • (1:Z))

local notation "invoice" lhs:max rhs:max => WilsonThermometerRegisteredCenteredInvoice.properInvoice lhs rhs
local notation "realFee" lhs:max rhs:max => WilsonThermometerRegisteredCenteredInvoice.restoration (fun v=>g*P.w v) lhs rhs

def coefficients (L:Poly (Stock.census (Fin 3))) (s:(Stock.census (Fin 3)).Mode):ℂ:=
  ∑ b,if Poly.merges s b full then L.part b else 0

theorem coefficients_read (tab₀ L:Poly (Stock.census (Fin 3))) :
    (tab₀*L).part full=WilsonGeometricSignedCapture.take (coefficients L) tab₀:=by
  simp only [Poly.part_mul,WilsonGeometricSignedCapture.take,coefficients,Finset.sum_mul]
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _
  by_cases ok:Poly.merges a b full <;> simp [ok,mul_comm]

include course in
theorem original (way:WayStation R.kit) (ticket:TicketP R.alloy R.kit D bank)
    {u j:ℕ} (floor:m≤u) (age:u ≤ i) (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ))≤u)
    (ju:j≤u) (door:Trace.Physical.GermGraph.Opened R.family 0 u per)
    (qual:WilsonThermometerUnitFilingShapeReceived.Qualified R A simple UV)
    (x:Fin 3→Site (R.family.side N per)) (site:o.origin=atOrigin (offsets x))
    (refs:∀v:Fin 3,R.family.ref (WilsonPositionThermometerGradedSource.grade v).val≤N)
    (q target:ℕ) (α:ℝ) (y:Site (R.family.side i per)) (Q:Poly J)
    (unit:Q.part (J).quiet=1)
    {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy} (checked:A.station.checked f H A.horizon)
    (honest:∀j,A.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j) (active:A.station.k<N)
    (charged:paidStore q target y α (measured R A UV x) Q)
    (price:(J).Mode→ℝ)
    (arms:∀s,coefficients (invoice (measured R A UV x) Q) s≠0→
      Booked R.family N per 0 (Fₓ s) u (age.trans cut.le) ∧ paid price s u j):
    let obs:=measured R A UV x
    let L:=invoice obs Q
    let d:ℂ:=realFee obs Q
    let model:=fun U=>((Ψ i).eval U:ℂ)*((submitted₀ U)*L).part full
    let older:=WilsonThermometerUnitFilingCoarse.reading R (N:=N) model u age-(Q*L).part full
    let price₂:=(‖d‖+‖1-d‖)*(units target+5*cost₁ q target α)
    ‖WilsonThermometerCenteredScalar.read (Extra.Trajectories.connected obs) univ-WilsonThermometerCenteredScalar.read (Extra.Trajectories.connected Q) univ-older‖≤
      (∑s,‖coefficients L s‖*price s)+price₂:=by
  intro obs L d model older price₂
  obtain ⟨b,h,blank,tinted,joined⟩:=charged
  have node : 0≤cost₁ q target α:=by
    have pos:0<g:=by
      have beta:=congrArg Coat.gStep (course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).beta
      exact beta ▸ P.issued.Waffle.soon.1
    positivity
  have trial:=WilsonThermometerReflectedTwoBills.original R A simple way D bank ticket π Γ Ψ course
    cut.le floor age gate o qual ju door (coefficients L) price arms y model d (1-d) b h node node
    blank.1 tinted.1 blank.2.1 tinted.2.1 (fun U=>by
      rw [←coefficients_read]; have balance:=joined U;dsimp only [L,obs,model,d]
      linear_combination balance)
  have unitBound (v:Coefficient (F) (R.family.side i per)) (fit:(F).coeffSize v.x≤units target) :
      ‖v.x 0‖≤units target :=
    (Finset.single_le_sum (fun j _=>norm_nonneg (v.x j)) (Finset.mem_univ 0)).trans fit
  have left:=unitBound b blank.2.2.2
  have right:=unitBound h tinted.2.2.2
  rw [←coefficients_read,site,←WilsonThermometerRegisteredAncestralProperTest.translated_table R A refs x] at trial
  have full_unit:obs.part (J).quiet=1:=WilsonThermometerRegisteredCenteredConnectedTest.measured_unit R A checked honest UV active refs x
  have conn:=WilsonThermometerRegisteredCenteredInvoice.proper obs Q full_unit unit
  rw [conn,sub_mul]
  change ‖(obs*L).part full-(Q*L).part full-
    (WilsonThermometerUnitFilingCoarse.reading R (N:=N) model u age-(Q*L).part full)‖≤_
  rw [sub_sub_sub_cancel_right]
  apply trial.trans
  apply add_le_add le_rfl
  dsimp only [price₂];rw [add_mul]
  gcongr

end YM.Integration.WilsonThermometerNominatedConnectedStop
