import YM.Integration.WilsonReceivedCloseQNamedTrail
import YM.Integration.WilsonReceivedCloseQNamedSalary
import YM.Integration.WilsonReceivedCloseQSchool
import YM.Integration.WilsonReceivedCloseElectedProgram

/-! On the selected Wilson house, place the two original curvature source lists at adjacent meshes.
Choose both source salaries before perturbation order. The full physical vacuum may have an arbitrary earlier ultraviolet cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseQNamedProgram
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
local notation "d₀" => WilsonReceivedCloseQNamedSalary.degree R simple request freshQ u μ extra D income K Q
  books ahead (ch).ready (ch).station house.stamps (ch).education hire house.calendar house.licence.forecast
  (ch).station.1 upperJ upperQ upperLabels upperClock upperExtra upperOrder
local notation "currency" => WilsonReceivedCloseQNamedSalary.currency R simple request freshQ u μ extra D income K Q
  books ahead (ch).ready (ch).station house.stamps (ch).education hire house.calendar house.licence.forecast
  (ch).station.1 upperJ upperQ upperLabels upperClock upperExtra upperOrder
variable (comparison span shape:ℕ) (height angleCap cap ε:ℝ) (hp:0≤angleCap) (cp:0≤cap) (ep:0<ε)
local notation "prec₀" => WilsonReceivedCloseQSchool.precision (d₀) axes comparison
local notation "p₁" => WilsonReceivedCloseQSchool.precision (d₀) axes (comparison+1)
local notation "o₀" => WilsonReceivedCloseQSchool.degree (d₀) axes (rank) (comparison+1)
local notation "k₀" => WilsonReceivedCloseQSchool.vacuum (d₀) axes (rank) (roomSize) (comparison+1)
local notation "Sch" => WilsonReceivedCloseQSchool.school (d₀) axes (rank) (roomSize) (comparison+1)
local notation "opAt" j:max h:max => (Sch).room (Push.PriceCompiler.step_paid R.alloy.B.a (j+1)) h
local notation "sales" => WilsonReceivedCloseQSchool.resources (d₀) axes (rank) (roomSize) (comparison+1)

/-- The same complete physical density and all of its proper faces are presented before the marked inputs are tested. -/
def Heard : Prop :=
  ∀ᶠ m:ℕ in atTop,∀ j (floor:m≤j),PaceR.Close R shape cap m j →
    ∀ N (cut:j+1<N),∃ (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (hk:Burn.horizon (k₀)+2 ≤ R.alloy.B.a.clock.J m)
      (_lesson:Lesson (N:=N) R hk D Q π Γ (floor.trans (Nat.le_succ j))),
      PlanV.Path D R.alloy Q (Burn.horizon (k₀)) N m π Γ ∧
      ∀ per,∃ Ψ:∀l,RG.Rep G (R.family.side l per),Concourse R.alloy R.kit R.T π Γ m N per (k₀) Ψ ∧
        Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N) ∧
        ∀ (upperSites:V→Site (R.family.side ((j+1)+1) per)) (sites:V→Site (R.family.side (j+1) per))
          (upperOrders orders:V→ℕ), (∀v,upperOrders v≤upperOrder) → (∀v,orders v≤K) →
          WilsonReceivedCloseQNamedTrail.Receipt (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ)
            (u:=u) (μ:=μ) (extra:=extra) (D:=D) (income:=income) (K:=K) (hk:=hk) (Q:=Q) (π:=π)
            (Γ:=Γ) (Ψ:=Ψ) (books:=books) (floor:=floor) (cut:=cut)
            (op:=opAt j (hk.trans (R.alloy.B.a.fits.mono (floor.trans (Nat.le_succ j)))))
            (ahead:=ahead) (way:=(ch).ready) (ticket:=(ch).station) (warm:=house.stamps)
            (education:=(ch).education) (employment:=hire) (calendar:=house.calendar) (hospital:=house.licence.forecast)
            (pass:=(ch).station.1) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
            (upperExtra:=upperExtra) (upperOrder:=upperOrder) (order:=o₀) (shelf:=roomSize)
            (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders)
            (old:=old) (fresh:=fresh) (span:=span) (height:=height) (angleCap:=angleCap)
            comparison ε

include protection hp cp ep sep in
theorem original (whole:old∪fresh=univ) (load:gradeTotal old (fun _:V=>uGrade) (fun _:V=>lGrade) ≤ roomSize) :
    Heard R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u upperLabels μ upperClock
      extra upperExtra K upperOrder old fresh comparison span shape height angleCap cap ε := by
  have feeRel:p₁=prec₀+1 := by unfold WilsonReceivedCloseQSchool.precision;omega
  have deep₁:= (sales).1
  change 2*(p₁+1)+8≤o₀ at deep₁
  have aged₁:= (sales).2.1
  have deep:2*(prec₀+1)+8≤o₀ := by omega
  have aged:prec₀+4≤3*(k₀)+2 := by omega
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
    protection p₁ span deep₁ aged₁ height angleCap hp (zero_lt_one:(0:ℝ)<1) shape axes prec₀ cp (zero_lt_one:(0:ℝ)<1)
  have wages:=WilsonReceivedCloseStationCalendar.original R simple D φ protection
    (choice old (fun _:V=>uGrade) (fun _:V=>lGrade)) (k₀) o₀ roomSize axes axes d₀ comparison prec₀
    span shape currency height angleCap cap ε (le_max_left ..) deep aged hp cp ep
  have paidFee:=eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
    (show 0 ≤ 2*(3:ℝ)^(prec₀+1) from mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)) (zero_lt_one:(0:ℝ)<1))
  filter_upwards [eventually_ge_atTop onset,payments,R.alloy.B.a.fits.deep.eventually_ge_atTop (k₀),
    R.alloy.B.a.fits.deep.eventually_ge_atTop (roomSize),wages,eventually_ge_atTop paidFee.choose] with m hm installed stage room windows smallPaid
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
  have shot:=WilsonReceivedCloseQNamedBirth.original (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ)
    (u:=u) (μ:=μ) (extra:=extra) (D:=D) (income:=income) (K:=K) (hk:=hk) (Q:=Q) (π:=π)
    (Γ:=Γ) (Ψ:=Ψ) (course:=ledger.conc) (path:=path) (books:=books) (floor:=floor) (cut:=cut)
    (op:=op) (lesson:=l) (ahead:=ahead) (way:=(ch).ready) (ticket:=(ch).station) (warm:=house.stamps)
    (education:=(ch).education) (employment:=hire) (calendar:=house.calendar) (hospital:=house.licence.forecast)
    (pass:=(ch).station.1) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
    (upperExtra:=upperExtra) (upperOrder:=upperOrder) (target:=comparison) (order:=o₀) (shelf:=roomSize)
    (upperRank:=hupper) (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders)
    (old:=old) (fresh:=fresh) (sep:=sep) (protection:=protection) (prec:=p₁) (span:=span) (deep:=deep₁)
    (aged:=aged₁) (height:=height) (angleCap:=angleCap) (capPos:=hp)
    scroll (ch) house.licence.monthly rfl rfl rfl rfl ledger.topline room upperOK lowerOK hlower load
    prec₀ shape cp feeRel (installed j floor) (smallPaid.trans floor) closeDates
  have orderFits:axes+(comparison+(2*d₀+1)*axes+1)≤o₀+1 := by
    have base:=deep
    change 2*((2*d₀*axes+(comparison+(2*d₀+1)*axes+1+axes)+3)+1)+8≤o₀ at base
    omega
  exact WilsonReceivedCloseQNamedTrail.original (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ)
    (u:=u) (μ:=μ) (extra:=extra) (D:=D) (income:=income) (K:=K) (hk:=hk) (Q:=Q) (π:=π)
    (Γ:=Γ) (Ψ:=Ψ) (course:=ledger.conc) (path:=path) (books:=books) (floor:=floor) (cut:=cut)
    (op:=op) (lesson:=l) (ahead:=ahead) (way:=(ch).ready) (ticket:=(ch).station) (warm:=house.stamps)
    (education:=(ch).education) (employment:=hire) (calendar:=house.calendar) (hospital:=house.licence.forecast)
    (pass:=(ch).station.1) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
    (upperExtra:=upperExtra) (upperOrder:=upperOrder) (order:=o₀) (shelf:=roomSize)
    (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders) (old:=old) (fresh:=fresh)
    (sep:=sep) (protection:=protection) (span:=span) (height:=height) (angleCap:=angleCap) (capPos:=hp)
    scroll (ch) house.licence.monthly house.licence.edges
    (by dsimp [WilsonReceivedCloseQSchool.vacuum, WilsonReceivedCloseQSchool.school, Burn.horizon]; omega) room
    (by change axes ≤ Burn.horizon (k₀)+2; dsimp [WilsonReceivedCloseQSchool.vacuum,Burn.horizon]; omega)
    (by dsimp [WilsonReceivedCloseQSchool.vacuum, WilsonReceivedCloseQSchool.school, Burn.horizon]; omega) stage
    prec₀ comparison shape cp ep deep aged (windows j floor) closeDates le_rfl orderFits whole shot

include protection hp cp ep sep in
/-- A single filed field alphabet at both dates meets the space invoice for every full partition
of its finite names into previously placed and genuinely new plaquettes. -/
theorem registered (whole:old∪fresh=univ) :
    Heard R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u u μ upperClock
      extra upperExtra K upperOrder old fresh comparison span shape height angleCap cap ε := by
  apply original R simple D Q scroll books ahead house protection income hire request upperJ freshQ upperQ u u
    μ upperClock extra upperExtra K upperOrder old fresh sep comparison span shape height angleCap cap ε
    hp cp ep whole
  simp [gradeTotal,choice]

end YM.Integration.WilsonReceivedCloseQNamedProgram

