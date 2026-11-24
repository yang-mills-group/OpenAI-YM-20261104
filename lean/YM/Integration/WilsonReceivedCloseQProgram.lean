import YM.Integration.WilsonReceivedClosePostedQ
import YM.Integration.WilsonReceivedCloseQSchool
import YM.Integration.WilsonReceivedCloseElectedProgram

/-! On the selected Wilson house, place the two original curvature source lists at adjacent meshes.
Choose both source salaries before perturbation order. The full physical vacuum may have an arbitrary earlier ultraviolet cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseQProgram
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra
open QuadraticLocal.Rebirth ConnectedActivityE6 FullQLocal FullQLocal.RenderedStep
open Multi Exterior WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open Source Labels LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonMixedPassportVote
open Pert.Asymptotics Extra.Histories WilsonOriginalReceivedChain
open scoped Classical BigOperators
open VowsR QuadraticLocal.Affinity Sycamore
variable {G:Gauge} (R:Run G) (simple:G.Simple)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  {φ:ℕ→ℕ} (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (ahead:Mentor.Forecast D R.rolls Q φ books) {ZΘ:ℝ} {profile:PhysicalNext.ThroughLaunch.Orders}
  (house:Treehouse.VariableHouse R D Q scroll books ZΘ ahead profile)
  (protection:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
  (hire:∀d,MintClock.Employment D φ d (R.rolls.L d))
  {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
  (request upperJ:Request V) (freshQ upperQ:MS.Land.Prescription B)
  (u upperLabels:V→MS.Rake.Label B) (μ upperClock:ℝ) (extra upperExtra:V→ℕ)
  (K upperOrder:ℕ) (old fresh:Finset V) (sep:Disjoint old fresh)
local notation "axes" => Fintype.card V
local notation "uGrade" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) upperLabels
local notation "lGrade" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "roomSize" => axes*uGrade
local notation "rank" => max (ActualOriginalQLayout.rankCap R upperLabels) (ActualOriginalQLayout.rankCap R u)
local notation "ch" => house.licence.employed
local notation "d₀" => WilsonReceivedCloseQCalendar.birthOrder R simple request freshQ u μ extra D income K Q
  books ahead (ch).ready (ch).station house.stamps (ch).education hire house.calendar house.licence.forecast
  (ch).station.1 upperJ upperQ upperLabels upperClock upperExtra upperOrder
variable (comparison span shape:ℕ) (height angleCap cap ε:ℝ) (hp:0≤angleCap) (cp:0≤cap) (ep:0<ε)
local notation "prec₀" => WilsonReceivedCloseQSchool.precision (d₀) axes comparison
local notation "o₀" => WilsonReceivedCloseQSchool.degree (d₀) axes (rank) comparison
local notation "k₀" => WilsonReceivedCloseQSchool.vacuum (d₀) axes (rank) (roomSize) comparison
local notation "Sch" => WilsonReceivedCloseQSchool.school (d₀) axes (rank) (roomSize) comparison
local notation "opAt" j:max h:max => (Sch).room (Push.PriceCompiler.step_paid R.alloy.B.a (j+1)) h
local notation "sales" => WilsonReceivedCloseQSchool.resources (d₀) axes (rank) (roomSize) comparison

/-- The same complete physical density and all of its proper faces are presented before the marked inputs are tested. -/
def Heard : Prop :=
  ∀ᶠ m:ℕ in atTop,∀ j (floor:m≤j),PaceR.Close R shape cap m j →
    ∀ N (cut:j+1<N),∃ (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (hk:Burn.horizon (k₀)+2 ≤ R.alloy.B.a.clock.J m)
      (lesson:Lesson (N:=N) R hk D Q π Γ (floor.trans (Nat.le_succ j))),
      PlanV.Path D R.alloy Q (Burn.horizon (k₀)) N m π Γ ∧
      ∀ per,∃ Ψ:∀l,RG.Rep G (R.family.side l per),Concourse R.alloy R.kit R.T π Γ m N per (k₀) Ψ ∧
        Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N) ∧
        ∀ (upperSites:V→Site (R.family.side ((j+1)+1) per)) (sites:V→Site (R.family.side (j+1) per))
          (upperOrders orders:V→ℕ), (∀v,upperOrders v≤upperOrder) → (∀v,orders v≤K) →
          WilsonReceivedClosePostedQ.Receipt (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ)
            (u:=u) (μ:=μ) (extra:=extra) (D:=D) (income:=income) (K:=K) (hk:=hk) (Q:=Q) (π:=π)
            (Γ:=Γ) (Ψ:=Ψ) (books:=books) (floor:=floor) (cut:=cut)
            (op:=opAt j (hk.trans (R.alloy.B.a.fits.mono (floor.trans (Nat.le_succ j)))))
            (lesson:=lesson) (ahead:=ahead) (way:=(ch).ready) (ticket:=(ch).station) (warm:=house.stamps)
            (education:=(ch).education) (employment:=hire) (calendar:=house.calendar) (hospital:=house.licence.forecast)
            (pass:=(ch).station.1) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
            (upperExtra:=upperExtra) (upperOrder:=upperOrder) (order:=o₀) (shelf:=roomSize)
            (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders)
            (old:=old) (fresh:=fresh) (sep:=sep) (span:=span) (height:=height) (angleCap:=angleCap)
            axes comparison ε

include protection hp cp ep in
theorem original (load:gradeTotal old (fun _:V=>uGrade) (fun _:V=>lGrade) ≤ roomSize) :
    Heard R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u upperLabels μ upperClock
      extra upperExtra K upperOrder old fresh sep comparison span shape height angleCap cap ε := by
  have deep:= (sales).1
  have aged:= (sales).2.1
  have hupper:ActualOriginalQLayout.rankCap R upperLabels ≤ o₀ := (le_max_left ..).trans (sales).2.2
  have hlower:ActualOriginalQLayout.rankCap R u ≤ o₀ := (le_max_right ..).trans (sales).2.2
  have big:2≤(Sch).order := (by omega : 2 ≤ 2*((prec₀)+1)+8).trans deep
  have visit:=house.across (k₀) (Sch) 0 0 0 0 0 0 shape 0 (1/16) 0 (1/8) 1 cap 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) cp
    (by norm_num) (by norm_num) big (by norm_num)
  obtain ⟨onset,bought⟩:=eventually_atTop.1 visit
  have payments:=WilsonReceivedCloseQCalendar.original R simple request freshQ u μ extra D income K (k:=k₀) Q
    books ahead (ch).ready (ch).station house.stamps (ch).education hire house.calendar house.licence.forecast
    (ch).station.1 upperJ upperQ upperLabels upperClock upperExtra upperOrder comparison o₀ (roomSize) hupper old
    protection prec₀ span deep aged height angleCap hp (zero_lt_one : (0:ℝ)<1) shape axes comparison cp ep
  filter_upwards [eventually_ge_atTop onset,payments,R.alloy.B.a.fits.deep.eventually_ge_atTop (k₀),
    R.alloy.B.a.fits.deep.eventually_ge_atTop (roomSize)] with m hm installed stage room
  intro j floor closeDates N cut
  have hi:=floor.trans (Nat.le_succ j)
  obtain ⟨v,_⟩:=bought j (hm.trans floor) m floor closeDates
  obtain ⟨π,Γ,hk,lessons,path,periods⟩:=v.era floor N ((Nat.le_succ j).trans cut.le)
  let l:=lessons (j+1) hi cut
  let op:=opAt j (hk.trans (R.alloy.B.a.fits.mono hi))
  refine ⟨π,Γ,hk,l,path,?_⟩
  intro per
  obtain ⟨Ψ,ledger⟩:=periods per
  refine ⟨Ψ,ledger.conc,ledger.topline,?_⟩
  intro upperSites sites upperOrders orders upperOK lowerOK
  exact WilsonReceivedClosePostedQ.issued (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ)
    (u:=u) (μ:=μ) (extra:=extra) (D:=D) (income:=income) (K:=K) (hk:=hk) (Q:=Q) (π:=π)
    (Γ:=Γ) (Ψ:=Ψ) (course:=ledger.conc) (path:=path) (books:=books) (floor:=floor) (cut:=cut)
    (op:=op) (lesson:=l) (ahead:=ahead) (way:=(ch).ready) (ticket:=(ch).station) (warm:=house.stamps)
    (education:=(ch).education) (employment:=hire) (calendar:=house.calendar) (hospital:=house.licence.forecast)
    (pass:=(ch).station.1) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
    (upperExtra:=upperExtra) (upperOrder:=upperOrder) (target:=comparison) (order:=o₀) (shelf:=roomSize)
    (upperRank:=hupper) (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders)
    (old:=old) (fresh:=fresh) (sep:=sep) (protection:=protection) (prec:=prec₀) (span:=span) (deep:=deep)
    (aged:=aged) (height:=height) (angleCap:=angleCap) (capPos:=hp) (kp:=(zero_lt_one:(0:ℝ)<1))
    scroll (ch) house.licence.monthly rfl rfl rfl rfl ledger.topline room stage upperOK lowerOK hlower load
    house.licence.edges le_rfl shape axes comparison cp ep le_rfl (installed j floor) closeDates
end YM.Integration.WilsonReceivedCloseQProgram
