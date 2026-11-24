import YM.Integration.WilsonOriginalCensusCanonicalDegree
import YM.Integration.WilsonOriginalCensusCanonicalRetainedClock
import YM.Integration.WilsonOriginalCensusCanonicalTopStamp
import YM.Integration.WilsonReceivedDepositedOrbitalIssuedFilter

/-! The post-kinetic canonical coefficient on the original awarded lower pupil
is the cofinal, compatibly addressed first Wick return at every retained age. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalCofinalReset
open Filter Function Finset Lattice Wilson RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn
open Comparison.RG02 AllOrder AllOrder.Floe PhysicalNext.Repeat.Legato FVA1Physical.TwoReset
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic WilsonThermometerDeclaredSeeds
open WilsonOriginalCensusCanonicalRows (row)
open WilsonOriginalMixedBlockRows (room)
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open Precision Tree Exterior Bloch Pressure Push
open AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series Further.PhysicalPeriodLimitF933 Macrame
open WilsonOriginalCopiedContraction WilsonOlderFreshGraphSlate
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open QuadraticLocal.Affinity QuadraticLocal.Sunrise QuadraticLocal.Poetry
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org AllOrder.Transit
open PhysicalNext.Repeat PhysicalNext.Repeat.Boulevard Push.PriceCompiler AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison ConnectedActivityE6
open QuadraticLocal.Rebirth PhysicalNext VowsR
open WilsonOriginalCensusCanonicalTopCopies (origins)
open WilsonOriginalCensusCanonicalPageFold (folded)
open WilsonOriginalRawQReversion (coordinates)
open WilsonNeutralSignedPolynomialRate (read)
open WilsonReceivedDepositedOrbitalIssuedFilter (fieldRow share)
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Wheel.Mark
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V]
local notation "J" => Stock.census V
variable (R:Run G){m i N per k:ℕ}
  (hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ→ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(hi:m ≤ i)(cut:i<N)
  (ahead:Mentor.Forecast D R.rolls Q φ books)(pieces:V→Submodule ℝ ℂ)(d:V→ℕ)(order shelf seats:ℕ)
  (physical:Wallet (room V) → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (room V) pieces d
    order shelf seats i hi physical)
  {heights:V→ℕ}(pt:V→Chamber)(q:(j:V)→Choice R d j)(hd:∀j,0 < d j)
  (o:V→Site (R.family.side (i+1) per))(σ:ℝ)
local notation "raw" => WilsonOriginalCensusCanonicalRows.row R d q hd o σ
local notation "tape₀" => Step.tape (Burn.horizon k+2)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead (room V) P.model order P.voter
local notation "zero₀" => Oak.grade0 R hk D Q π Γ hi P.lesson
local notation "stamped" => Mutation.stamp (student) (Γ i) (zero₀) (Burn.horizon k+2) order
include course cut in
theorem original (placed:P.passport=Passport.point o)(names:P.modelIndex=V)(ink:HEq P.model (raw))
    (pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)(fits:order≤Burn.horizon k+1)
    (narrow:shelf≤R.alloy.B.a.clock.J i){quiet:ℕ→SeriesA G}(actual:Read R N m (Burn.horizon k) quiet π Γ)
    {τ cash:ℝ}(funded:Issued R N (i+1) (Burn.horizon k) (quiet (i+1)) τ cash)(simple:G.Simple)
    (x:Wallet (room V))(grid:Side)(tiles:(R.family.side i per).val∣grid.val)
    (tags:∀b:Covers R.family.path.levels.S i grid,(step R i b.val).Choices)
    (s:Multi.Hot (J))(v:Stationary.Link G grid)(r a:ℕ)(through:r≤order)(kept:a≤r):

    let series:=fun b:Covers R.family.path.levels.S i grid=>
      let sites:=origins R d q hd o σ grid tiles b
      let times:=ratioHigh (WilsonVacuumPreResetStationaryChange.levels R) R.metals.O N i
      folded sites (WilsonOriginalCensusCanonicalKinetic.connected (h:=heights) R d pt q N i b.val
        (repeatF (step R i b.val)) times) s.val.val
    Tendsto (fun b=>share R grid b*((∏j∈s.val.val,(x j).val)*read (coordinates G (coarse R i b.val))
      (series b) a (AllOrder.Ker.convey (coverWin b.prop) v))) (coverFilter R.family.path.levels.S i grid)
      (𝓝 ((peek tiles (stamped) d (π i) (tape₀) x a v).part s.val)):=by
  intro series
  let colors:=fun b:Covers R.family.path.levels.S i grid=>copyColor (tiled R tiles b) P.model d
    (fun j=>(P.model j).paint x) (π (i+1)) (tape₀)
  let trees:=fun b:Covers R.family.path.levels.S i grid=>repeatF (step R i b.val)
  let sites:=origins R d q hd o σ grid tiles
  have vote:=WilsonOriginalReceivedCopiedCover.published R hk D Q π Γ Ψ course books hi cut ahead
    (room V) pieces d order shelf seats physical P
  have legal:Legal (tape₀) (π (i+1)):=by
    rw [P.lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ P.lesson.entry
  have normalized (b:Covers R.family.path.levels.S i grid):
      fieldRow R cut order grid colors trees tags s.val b=
        WilsonOriginalCensusCanonicalMeasuredReset.hearing (h:=heights) R d pt q N i b.val (trees b)
          x (sites b) order s.val.val:=by
    funext l z
    have paid:=WilsonOriginalCensusCanonicalTopBoard.original (h:=heights) R d pt q hd o σ N i b.val cut
      (trees b) (tags b) (tiled R tiles b) x (π (i+1)) (tape₀) (sites b) (fun j v=>wrap_lift _)
      P.model placed names ink P.salary (Poetry.Agenda.stem ..) legal actual hi funded simple z order (by omega)
    exact congrArg (fun C=>(Order.observe (J) order C l).part s.val) paid.2
  have issued:=WilsonOriginalRetainedStamp.original (R:=R) (hk:=hk) (course:=course) (cut:=cut)
    (pass:=pass) (month:=month) (fits:=fits) (narrow:=narrow) (issued:=P.issued.earning)
    (x:=x) (h:=tiles) (small:=through) (kept:=kept) (s:=s) (z:=v)
    (value:=fun l z=>peek tiles (student) d (π (i+1)) (tape₀) x l z) (source:=fun _ _ _=>rfl)
  rw [issued]
  have rate:=WilsonReceivedDepositedOrbitalIssuedFilter.original (R:=R) (h:=cut) (M:=P.model)
    (Y:=(student)) (published:=vote) (t:=x) (grid:=grid) (inputs:=colors) (trees:=trees) (tags:=tags)
    (multiple:=tiles) (matched:=fun _=>rfl) (cost:=(Rebirth.caliber (Γ i) (zero₀)).back (Burn.horizon k+2))
    (r:=r) (d:=a) (kept:=through) (s:=s) (height:=fun l=>mass d s.val.val+l) (Z:=v)
    (fund:=fun b l hl=>by
      rw [normalized b]
      exact WilsonOriginalCensusCanonicalDegree.original (h:=heights) R d pt q N i b.val cut
        x (sites b) simple order s.val.val l (hl.trans through))
  apply rate.congr'
  apply Eventually.of_forall
  intro b
  change share R grid b*Adjacent.born (fieldRow R cut order grid colors trees tags s.val b) _ 0 r a _ = share R grid b*_
  rw [normalized b]
  apply congrArg (share R grid b*·)
  exact WilsonOriginalCensusCanonicalRetainedClock.original (h:=heights) R d pt q
    N i b.val cut (trees b) x (sites b) actual.course hi (zero₀) simple order r a through (by omega) kept
    s.val.val (AllOrder.Ker.convey (coverWin b.prop) v)

end YM.Integration.WilsonOriginalCensusCanonicalCofinalReset
end
