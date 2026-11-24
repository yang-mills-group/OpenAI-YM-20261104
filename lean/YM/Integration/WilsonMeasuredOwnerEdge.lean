import YM.Integration.WilsonMeasuredOwnerPaid
import YM.Integration.WilsonMeasuredOwnerKernel
import YM.Integration.WilsonMeasuredOwnerReturn
import YM.Integration.WilsonMeasuredOnlyHard

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerEdge
open YM.Integration.WilsonMeasuredOwnerReserve
open Labels Source WilsonPhysicalMarkedDefect.RegularProjection
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology
open WilsonThermometerCourseHearing
variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)


variable (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i floor physical)
open Pert.Asymptotics Extra.Histories Trace.Physical.GermGraph Trace.Physical
open RG16 WilsonMeasuredCoefficientTransport
open Progress.DirectedRecipe QuadraticLocal.Tint

local notation "incoming" => Ψ (i+1)
local notation "κ₁" => LocalComparison.forcedDivisor R.family (i+1)
local notation "κ₀" => LocalComparison.forcedDivisor R.family i
local notation "cash" => R.family.path.levels.clock.forcedAllowance (i+1)
local notation "labels₁" => Stock.census (Fin 1)
local notation "temperature" => R.alloy.B.a.clock.hatBeta (i+1)

local notation "hc" => R.family.path.rep N per (i+1)
local notation "g₁" => Coat.gStep (hc).beta
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead order shelf
local notation "L₀" => ((R.family.S.block i).val:ℝ)
local notation "E₁" => Earn.Passport.point (fun _:Fin 1=>(0:Site (R.family.side (i+1) per)))
local notation "model₁" => (Empty.elim : Empty → Row (E₁) (labels₁) G (Wallet disk))
variable (rank:ℕ)
local notation "F₀" => R.family.labels.level rank
local notation "S₀" => R.family.localSection rank
local notation "Y₀" => R.family.params
local notation "scaleCost" => WilsonMeasuredRankedResidual.sourceCost R rank
local notation "wrap" => WilsonMeasuredRankedPrimaryBudget.wrap (F₀) Y₀

/-- One genuine standalone hard contribution in the original Wilson step at
origin zero. The returned coefficient retains its own original supports. -/
theorem original (ticket:V) (live:i<N) (simple:G.Simple)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (size:seats ≤ Burn.horizon k+2) (shelfFit:shelf ≤ R.alloy.B.a.clock.J i)
    (way:WayStation R.kit) (small:cash ≤ κ₁/2)
    (M:WilsonMeasuredRankedMenu.Menu R rank)
    (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (prepared:WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed:(R.family.path.levels.budget i).supportExponent ≤ 100)
    (date:R.t rank ≤ i) (active:M.onset ≤ i)
    (late:WilsonCenteredCaptureClock.first R simple ≤ i)
    (gross:WilsonReceivedSourceGross.opening R simple ≤ i)
    (fare:WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared ≤ i)
    (q:ℕ) (ready:q+6 ≤ R.alloy.B.a.clock.J i) (deep:2*(q+4+1)+8 ≤ order)
    (aged:q+4+4 ≤ 3*k+2)
    (opening:WilsonFirstReceivedEarnedFee.opening R simple P.op.count (q+4) order k deep aged
      (show (0:ℝ)<1 by norm_num) ≤ i)
    (cool:g₁ ≤ 1)
    (h:Coefficient (F₀) (R.family.side (i+1) per)) (B w:ℝ)
    (format:h.Format 0 Y₀ (incoming)) (bill:h.remBound 0 (incoming) κ₁ B)
    (wp:0<w) (fit:w*B ≤ 1/2) :
    ∃ (z:Coefficient (F₀) (R.family.side i per)) (u:ℝ), z.Format 0 Y₀ (Ψ i) ∧
      z.remBound 0 (Ψ i) κ₀ u ∧ (F₀).coeffSize z.x ≤ u ∧
      GermGraph.transition (C:=R.family) rank N per i (account h (incoming)) = z.density 0 S₀ (Ψ i) ∧
      w*u ≤ L₀^rank*(WilsonMeasuredOwnerFare.unitCost scaleCost M.cost wrap q*g₁^q) := by
  let τ:=min 1 (g₁^(q+4)/(8*Ω^P.op.count))
  have gp:= (WilsonMeasuredRankedPrimaryBudget.native R simple live per).1
  have Ωp:=P.issued.Waffle.paysAbove
  have pay:0<8*Ω^P.op.count:=mul_pos (by norm_num) (pow_pos Ωp _)
  have τp:0<τ:=lt_min zero_lt_one (div_pos (pow_pos gp _) pay)
  have spend:(8*Ω^P.op.count)*τ ≤ g₁^(q+4):=by
    rw [mul_comm]
    exact (le_div_iff₀ pay).mp (min_le_right _ _)
  obtain ⟨Z,L,op,lesson,stamp,width,cost,rent,_,_,count,fired,_⟩:=WilsonMeasuredOwnerReturn.original
    R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P 0 ticket live simple
    course scroll chamber hospital size shelfFit way small S₀ Y₀ h format B w bill wp fit τp (min_le_left _ _)
  letI:=count
  let x: Wallet disk:=fun _=>⟨1,by simp [disk]⟩
  let src:=(Tint.Patrol.picture (model₁) Z).density
  have reference: P.op.count ≤ Burn.horizon k+2:=P.capacity.trans_le size
  obtain ⟨A,b,shape,paid,profile,price⟩:=WilsonMeasuredOwnerPaid.original R hk D Q π Γ Ψ course books floor live
    ahead disk kernel (fun _=>0) order shelf seats src L rank cost M simple way slow prepared fixed date
    active late gross fare pass hospital shelfFit (by simpa only [op] using reference) q ready deep aged
    (by simpa only [op] using opening) cool (by simpa only [op,lesson,rent] using spend) x 0
  let link:=R.family.path.levels.clock.op i per
  have zero:(L.passport.coarser link.ratio).origin 0=0:=by
    rw [stamp]
    change link.ratio.parent 0=0
    exact (show link.ratio.embed 0=0 from link.ratio.root.map_zero) ▸ link.ratio.embed_parent 0
  change A.Format ((L.passport.coarser link.ratio).origin 0) Y₀ (Ψ i) at shape
  change A.remBound ((L.passport.coarser link.ratio).origin 0) (Ψ i) κ₀ b at paid
  change ∀U,A.density ((L.passport.coarser link.ratio).origin 0) S₀ (Ψ i) U=
    (LocalComparison.actualPush R.family N per i (src x) U).part ((labels₁).fire 0) at profile
  rw [zero] at shape paid profile
  rw [width] at price
  obtain ⟨same,owners,-⟩:=WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course (floor.trans i.le_succ) live
  have eq: (incoming).eval=(hc).eval:=(course.1.walk (i+1) (floor.trans i.le_succ) live).view
  have split:=(WilsonMeasuredOnlyHard.original h hc (incoming) same eq owners S₀ Y₀ 0 κ₁ B format bill).2.2.1
  have honest (U): (src x U).part ((labels₁).fire 0)=account h (incoming) U := by
    rw [(fired x U).2,split U]
    change 1*(_ + _ - _) = _
    ring
  have measured:=WilsonMeasuredOwnerKernel.transition R hk D Q π Γ Ψ course books floor live ahead
    disk kernel (fun _=>0) order shelf seats src L x ((labels₁).fire 0) rank (account h (incoming)) honest
  let alpha:=((R.family.S.block i).val:ℂ)^rank
  let u:=L₀^rank*(b+(F₀).coeffSize A.x)
  have scaledNorm:‖alpha‖=L₀^rank:=by simp [alpha]
  have lp:0 ≤ L₀^rank:=by positivity
  have bp:0 ≤ b:=Extra.Histories.rem_nonneg paid
  have xp:0 ≤ (F₀).coeffSize A.x:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨stretch alpha A,u,stretch_format alpha shape,?_,?_,?_,?_⟩
  · apply Extra.Histories.rem_mono (stretch_rem alpha paid)
    rw [scaledNorm]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right xp) lp
  · change (F₀).coeffSize (alpha • A.x) ≤ u
    rw [Size.smul,scaledNorm]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left bp) lp
  · funext U
    rw [stretch_density,measured,profile U]
    rfl
  · calc
      _ = L₀^rank*(w*(b+(F₀).coeffSize A.x)):=by dsimp only [u];ring
      _ ≤ _:=mul_le_mul_of_nonneg_left price lp

end YM.Integration.WilsonMeasuredOwnerEdge
