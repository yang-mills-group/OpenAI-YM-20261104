import YM.Integration.WilsonOriginalNullBareRows
import YM.Integration.WilsonOriginalNullBareStock

/-! The actual signed terminal state on the registered point-word roster. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareTerminal
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m i N per k Q d:ℕ}
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (chamber:VowsR.Chamber scroll R.kit D Q₀ books) (hi:m ≤ i)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
  (school:Syl.School k)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q₀ π Γ hi)
  (cal:Oak.Calendar R hk D Q₀ π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀"=> Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
variable (sites:∀j,Site (R.family.side j per))
local notation "y" => sites (i+1)
local notation "S"=>WilsonOlderFreshGraphPointWallet.point y
local notation "letterPost"=>Earn.Passport.point (fun _:Unit=>y)

variable (A:Unit→Set ℂ)
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter

variable {dmax:ℕ} (L:Primer.Families R.family) (a:hue G) (depth:d<dmax)
    (w:Letter (R.family.labels.level d)) (f:Studio dmax)
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon

local notation "βhat"=>R.alloy.B.a.clock.hatBeta (i+1)

variable (digit:∀h,Site (R.family.S.block h))

open RG16 Pert.Asymptotics Trace.Physical.Germ Trace.Physical.GermGraph Extra.Histories
open WilsonCapturedPrimaryPaid WilsonCenteredFiledAtoms WilsonOlderSignedOneMarkTariff
local notation "W₁" => Ψ (i+1)
local notation "P₁" => R.family.path.rep N per (i+1)
local notation "Fr" => R.family.labels.level d
local notation "Sec" => R.family.localSection d
local notation "Y" => R.family.params
local notation "κ" => LocalComparison.forcedDivisor R.family (i+1)
local notation "fire" => (Stock.census Unit).fire ()
local notation "height" => grade 3 d 1
local notation "stamp" => (2:ℝ)^(school.order+school.horizon+1)
local notation "baseCost" => 8*Real.exp 102*(1+2*charge Y Sec)+2*Real.exp 102
local notation "unitCost" => WilsonOriginalNullBareGross.price stamp baseCost
  (WilsonCapturedPrimaryDecoder.invoice Fr Y d) (WilsonCapturedPrimaryCoreBill.wrapFee Fr Y) height
local notation "σ" => fun j=>Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J j)
local notation "axes" => Letter (R.family.labels.level d)
open WilsonOlderFreshLocatedBook
include history scroll chamber warm top cal hospital in
theorem original (simple:G.Simple)(nonbare:i<N)(cap:∀t,‖value A t‖≤1)
    {τ:ℝ}(pos:0<τ)(bounded:τ≤1)(pass:Pass D Q₀ R.alloy R.kit)
    (late:WilsonMeasuredSemesterSubpower.onset R 1 (half_pos (show (0:ℝ)<1 by norm_num)) ≤ i)
    (T:∀j,m ≤ j → j ≤ N → axes → Studio dmax → WilsonOlderFreshGraphSlate.Copy G d Q ((σ) j))
    (sheets:WilsonOlderFreshLocatedRoster.Booked R L a depth Q σ m N digit T)
    (seats:1≤op.count)(shape:op.count=school.pieces)(phase:school.order+1≤op.stage)
    (enrolled:Q ≤ school.order)(order:d ≤ school.horizon)(cut:ℕ)
    (width:Sycamore.Boot.need cut school ≤ R.alloy.B.a.clock.J (i+1))(test:Wallet A)
    (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (geo:WilsonOriginalNullBareCapital.Priced W₁ σ₀ school.order school.horizon school.pieces (budgetR R (i+1)))
    (fixed:(R.family.path.levels.budget (i+1)).supportExponent=100)
    (time:WilsonOriginalNullBareFunding.first R d simple slow ready ≤ i+1)
    (home:Opened R.family d (i+1) per)(upper:Fin (Q+1)→axes→ℂ) :
    let book:=WilsonOlderFreshLocatedBook.fixed R σ T sites (orbit R digit (m+1) f) A test (fun j=>Coat.gStep (Ψ j).beta)
    let cost:=2*|unitCost| *(1+R.alloy.B.a.clock.hatBeta ((i+1)+1))^(height+7)*(1+‖f‖)
    WilsonOriginalNullBareRows.Paid R (d:=d) (N:=N) W₁ y
      (fun U=>((W₁).eval U:ℂ)*WilsonTrueProjectedPointProgram.ordinary R (book (i+1)) upper U)
      ((∑l:axes,‖∑e:Fin (Q+1),upper e l‖)*cost) :=by
  classical
  intro book cost
  let c:=fun l:axes=>∑e:Fin (Q+1),upper e l
  let field:=fun (l:axes) (U:Config G (R.family.side (i+1) per))=>((W₁).eval U:ℂ)*book (i+1) l U
  have each (l:axes):WilsonOriginalNullBareRows.Paid R (d:=d) (N:=N) W₁ y (field l) cost:=
    WilsonOriginalNullBareCatalogue.original R hk D Q₀ π Γ Ψ history scroll books chamber hi warm top school op lesson
      cal ahead hospital sites A L a depth l f digit simple nonbare cap pos bounded pass late T sheets seats shape phase
      enrolled order cut width test slow ready geo fixed time home
  let tr:=(history.1.walk (i+1) (Nat.le_succ_of_le hi) nonbare).truep
  have same:(W₁).p=(P₁).p:=tr.point.trans (R.makes.wilson.represents N per (i+1) nonbare).vac.symm
  have bought:=WilsonOriginalNullBareRows.weighted R W₁ y tr.valid same nonbare home field
    (fun _=>cost) c each
  rw [←Finset.sum_mul] at bought
  have identity:(fun U=>((W₁).eval U:ℂ)*WilsonTrueProjectedPointProgram.ordinary R (book (i+1)) upper U)=∑l,c l • field l:=by
    funext U
    simp only [WilsonTrueProjectedPointProgram.ordinary,WilsonTrueProjectedFiledTransfer.submitted,
      WilsonTrueProjectedFiledTransfer.weighted,Finset.mul_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro l _
    dsimp [field,c];ring
  rw [identity]
  exact bought

end YM.Integration.WilsonOriginalNullBareTerminal
