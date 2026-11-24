import YM.Integration.WilsonMeasuredPointBasisAverage
import YM.Integration.WilsonMeasuredPointPhaseDebit
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointFrozenHearing
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m j N per k Q:ℕ}
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (chamber:VowsR.Chamber scroll R.kit D Q₀ books) (floor:m ≤ j)

local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "i₁" => (j+1)
variable
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
  (school:Syl.School k)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson:Lesson (N:=N) R hk D Q₀ π Γ (floor.trans (Nat.le_succ j)))
  (cal:Oak.Calendar R hk D Q₀ π Γ Ψ (floor.trans (Nat.le_succ j)) (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀"=> Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i₁+1))
variable (y:Site (R.family.side ((j+1)+1) per))
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
open WilsonOriginalReceivedChain WilsonMeasuredRankedResidual Pert.Asymptotics

variable {dmax:ℕ} (L:Primer.Families R.family) (a:hue G) (depth:(4:ℕ)<dmax)
    (pivot:(R.family.labels.level 4).Index) (f:Studio dmax)
local notation "w₄" => WilsonNeutralBilinearLetters.plain (R.family.labels.level 4) pivot
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon

local notation "βhat"=>R.alloy.B.a.clock.hatBeta (i₁+1)
local notation "massF"=>‖f‖

local notation "pieces" => (fun _ : Unit => (⊥ : Submodule ℝ ℂ))
local notation "grades" => (fun _ : Unit => (4:ℕ))
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G (4:ℕ) Q σ₀
local notation "birth" => (fun (T:slate) (x:Wallet A) (U:Config G (R.family.side (i₁+1) per)) =>
  ((Ψ (i₁+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (T.rows S A) (Coat.gStep (Ψ (i₁+1)).beta) x U))
local notation "down" => (fun (T:slate) (x:Wallet A) => LocalComparison.actualPush R.family N per i₁ (birth T x))
local notation "upper" => (fun (T:slate) => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A pieces grades school.order school.horizon school.pieces i₁ hi (birth T))
local notation "lower" => (fun (T:slate) => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A pieces grades school.order school.horizon school.pieces j floor (down T))
local notation "origin₁" => ((letterPost).coarser (R.family.path.levels.clock.op i₁ per).ratio).origin ()
local notation "u" => (Stock.census Unit).fire ()
local notation "p₁" => Ψ i₁
local notation "d₁" => R.family.labels.level (4:ℕ)
local notation "κ" => LocalComparison.forcedDivisor R.family i₁
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per j

local notation "stride₄" => ((R.family.path.levels.S.block i₁).val:ℝ)^4
local notation "tap" => (↑(stride₄):ℂ)
local notation "readout" => (fun (T:slate) (F:lower T) (x:Wallet A) (U:Config G (R.family.side i₁ per)) =>
  (down T x U).part u - ((p₁).eval U:ℂ)*(Spill.Foundry.uncut F.model (Coat.gStep (p₁).beta) x U).part u)
local notation "source₄" => Source.Coefficient (d₁) (R.family.side i₁ per)


local notation "FIndex" => (R.family.labels.level (4:ℕ)).Index

local notation "upperSide" => R.family.side (i₁+1) per
local notation "lowerSide" => R.family.side i₁ per
local notation "gu" => Coat.gStep (Ψ (i₁+1)).beta
local notation "sheet" => (fun (T:slate)(x:Wallet A)(U:Config G upperSide)=>
  (Spill.Foundry.uncut (T.rows S A) gu x U).part u)
open MeasureTheory


variable (station:WilsonPositionThermometerCapStation.Group R.family 6)(leg:Fin 2)(phase:ℂ→ₗ[ℝ]ℝ)
local notation "named" => WilsonNeutralOffsetCutoff.named R station N per leg.succ
local notation "coin" => (fun b:FIndex=> ((WilsonNeutralCopiedProgram.fee R N per named phase
  (Coat.gStep (R.family.beta N per)) b):ℂ))
local notation "topSize" => (d₁).coeffSize (Next.Rank.Price.awake R.family 4 N N per named)

private theorem swap {I J:Type*}[Fintype I][Fintype J](w:I→ℂ)(M:I→J→ℝ)(G₀:J→ℂ):
    (∑i:I,w i*(∑j:J,(M i j) • G₀ j))=(∑j:J,(∑i:I,w i*(M i j:ℂ))*G₀ j):=by
  simp only [Complex.real_smul,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  exact Finset.sum_comm

include history scroll chamber warm top in
theorem original (simple:G.Simple)(cut:i₁< N)(ready:R.family.ref 4≤ N)
    (T:FIndex→slate)(high:ℕ)(space:Sycamore.Boot.need high school≤R.alloy.B.a.clock.J (i₁+1))
    (stamped:∀v:FIndex,∃H:upper (T v),H.passport=letterPost ∧ H.modelIndex=(T v).Roster ∧
      HEq H.model ((T v).rows S A))
    {J:Type*}[Fintype J](alpha:FIndex→J→ℝ)(raw:J → Config G lowerSide → ℂ)
    (x:Wallet A)(amount:ℝ)(nonnegative:0≤amount)
    (columns:∀b:FIndex,∃(Z:source₄)(a:ℝ),Z.Format origin₁ R.family.params (p₁) ∧
      Z.remBound origin₁ (p₁) κ a ∧ a+(d₁).coeffSize Z.x≤amount ∧
      ∀U,Z.density origin₁ (R.family.localSection 4) (p₁) U=
        tap*(down (T b) x U).part u-((p₁).eval U:ℂ)*(∑v:J,(alpha b v) • raw v U)):
    ∃(E:source₄)(a:ℝ),E.Format origin₁ R.family.params (p₁) ∧ E.remBound origin₁ (p₁) κ a ∧
      a+(d₁).coeffSize E.x≤2*‖phase.toContinuousLinearMap‖*topSize*amount ∧
      ∀W,E.density origin₁ (R.family.localSection 4) (p₁) W=((p₁).eval W:ℂ)*(
        actualAverage R.family (N:=N) (fun U=>∑b:FIndex,(coin b*tap)*(sheet (T b) x U)) W-
        ∑v:J,(∑b:FIndex,coin b*(alpha b v:ℂ))*raw v W) :=by
  have lawful:=(history.1.walk i₁ hi cut.le).truep.valid
  have κpos:0<κ:=Real.sqrt_pos.mpr (Push.Local.allowance_pos R.family.path.levels.clock i₁)
  let push(b:FIndex)(U:Config G lowerSide):=tap*(down (T b) x U).part u
  let filed(b:FIndex)(U:Config G lowerSide):=∑v:J,(alpha b v) • raw v U
  obtain ⟨E,b,fmt,hard,read,wage⟩:=WilsonMeasuredPointPhaseDebit.original R N per station leg phase
    simple ready lawful κpos push filed amount nonnegative (fun v=>by
      obtain ⟨Z,a,form,paid,fee,row⟩:=columns v
      exact ⟨Z,a,form,paid,row,fee⟩)
  refine ⟨E,b,fmt,hard,wage,?_⟩
  intro W
  have joined:=WilsonMeasuredPointBasisAverage.original (R:=R) (N:=N) (hk:=hk) (D:=D) (Q₀:=Q₀)
    (π:=π) (Γ:=Γ) (Ψ:=Ψ) (history:=history) (scroll:=scroll) (books:=books) (chamber:=chamber)
    (floor:=floor) (warm:=warm) (top:=top) (school:=school) (ahead:=ahead) (y:=y) (A:=A)
    cut T high space stamped x (fun b=>coin b*tap) W
  refine (read W).trans ?_
  dsimp only [push,filed]
  rw [mul_sub]
  apply congrArg₂ (· - ·)
  · refine Eq.trans ?_ joined.symm
    apply Finset.sum_congr rfl
    intro b _
    exact (mul_assoc _ _ _).symm
  · exact congrArg (fun z:ℂ=>((p₁).eval W:ℂ)*z) (swap coin alpha (fun v=>raw v W))

end YM.Integration.WilsonMeasuredPointFrozenHearing
end
