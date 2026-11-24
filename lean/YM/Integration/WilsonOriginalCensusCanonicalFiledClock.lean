import YM.Integration.WilsonOriginalCensusCanonicalFiled
import YM.Integration.WilsonOriginalCensusCanonicalCofinalReset

/-! The retained measured response belongs to the appointed upper stencil
on the public Wilson history, with its genuine all-field wages. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalFiledClock
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

open WilsonOriginalCensusCanonicalRows WilsonOriginalMixedBlockRows WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords (rank)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open Filter MintClock XSpace Pert.Asymptotics

open WilsonVacuumPreResetStationaryChange (step coarse levels)
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonOriginalRawQReversion (coordinates)
open WilsonOriginalCensusCanonicalTopCopies (origins)
open WilsonOriginalCensusCanonicalPageFold (folded)
open WilsonReceivedDepositedOrbitalIssuedFilter (share)
open WilsonNeutralSignedPolynomialRate (read)
open FVA1Physical.TwoReset WilsonCoeffUV.Winding Further.PhysicalPeriodLimitF933 Macrame
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider.Canvas FreeResolvent
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Pressure Precision Tree Exterior PertExtension PertExtension.Series WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open scoped Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge} (R:Run G) (simple:G.Simple) {m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (hi:m ≤ i) (cut:i < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  {V:Type}[Fintype V][DecidableEq V](d:V→ℕ)(q:(j:V)→Choice R d j)(hd:∀j,0 < d j)
  (o:V→Site (R.family.side (i+1) per))(order shelf:ℕ)

local notation "H" => Ψ (i+1)
local notation "scale" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "M" => row R d q hd o scale
local notation "A" => room V
local notation "K₀" => (fun _:V=>(⊥:Submodule ℝ ℂ))
local notation "marks" => Stock.census V
local notation "w₀" => (fun _:V=>(1:ℝ))
local notation "C₀" => charge R d q scale w₀
local notation "g" => Coat.gStep (H).beta
local notation "D₀" => (∑v:V,d v)+1
local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "physical" => fun (x:Wallet (A))(U:Config G (R.family.side (i+1) per))=>
  ((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M (g) x U)
local notation "Ptype" => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (A) (K₀)
  d order shelf op.count i hi (physical)

local notation "S₀" => (fun _:V=>max 1 (C₀))
local notation "e₀" => ((D₀)+5)*Fintype.card V
local notation "rate" => fun s:(marks).Mode=>(R.alloy.B.a.clock.hatBeta i)^(e₀)*Poly.toll (S₀) s
local notation "pupil" F:max => Oak.student (n:=per) R hk D Q π Γ books hi (F).op (F).lesson
  ahead (A) (F).model order (F).voter


local notation "voucher" F:max => WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books hi ahead
  (A) (K₀) d order shelf op.count (physical) F (rate)
local notation "file" F:max B:max x:max => WilsonOriginalCensusCanonicalFiled.file
  R hk D Q π Γ Ψ books hi op ahead d q hd o order shelf F B x
local notation "pay" => Step.tape (Burn.horizon k+2)

def Returns (F:Ptype)(B:voucher F):Prop:=
  ∀(h:V→ℕ)(pt:V→Chamber)(x:Wallet (A))(s:Multi.Hot (marks))
    (z:Stationary.Link G (coarse R i per))(r a:ℕ),r≤order→a≤r→
    let issued:=file F B x
    let student₀:=Oak.student (n:=per) R hk D Q π Γ books hi issued.post.op issued.post.lesson ahead (A)
      issued.post.model issued.order issued.post.voter
    let restamp:=Mutation.stamp student₀ (Γ i) (Oak.grade0 R hk D Q π Γ hi issued.post.lesson) (Burn.horizon k+2) issued.order
    let panel:=fun b:Covers R.family.path.levels.S i (coarse R i per)=>
      let sites:=origins R d q hd o (scale) (coarse R i per) dvd_rfl b
      let times:=ratioHigh (levels R) R.metals.O N i
      folded sites (WilsonOriginalCensusCanonicalKinetic.connected (h:=h) R d pt q N i b.val
        (repeatF (step R i b.val)) times) s.val.val
    Tendsto (fun b=>share R (coarse R i per) b*((∏j∈s.val.val,(x j).val)*
      read (coordinates G (coarse R i b.val)) (panel b) a (AllOrder.Ker.convey (coverWin b.prop) z)))
      (coverFilter R.family.path.levels.S i (coarse R i per))
      (𝓝 ((peek dvd_rfl restamp issued.grades (π i) (pay) issued.x a z).part s.val))

include course cut simple in
theorem onFiled (F:Ptype)(B:voucher F)(placed:F.passport=Passport.point o)(names:F.modelIndex=V)(ink:HEq F.model (M))
    (pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (capacity:order+(∑v,d v)≤Burn.horizon k+2)(narrow:shelf≤R.alloy.B.a.clock.J i)
    {quiet:ℕ→SeriesA G}(actual:Read R N m (Burn.horizon k) quiet π Γ)
    {τ cash:ℝ}(credit:Issued R N (i+1) (Burn.horizon k) (quiet (i+1)) τ cash)
    (tags:∀b:Covers R.family.path.levels.S i (coarse R i per),(step R i b.val).Choices):
    Returns R hk D Q π Γ Ψ books hi op ahead d q hd o order shelf F B:=by
  intro h pt x s z r a kept grade
  have pos:0<∑j,d j:=
    lt_of_lt_of_le (hd s.prop.choose) (single_le_sum (fun j _=>Nat.zero_le (d j)) (mem_univ s.prop.choose))
  exact WilsonOriginalCensusCanonicalCofinalReset.original (heights:=h) R hk D Q π Γ Ψ course books hi cut
    ahead (K₀) d order shelf op.count (physical) F pt q hd o (scale) placed names ink pass month
    (by omega) narrow actual credit simple x (coarse R i per) dvd_rfl tags s z r a kept grade

end YM.Integration.WilsonOriginalCensusCanonicalFiledClock
end
