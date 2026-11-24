import YM.Integration.WilsonOriginalTwoFlatIRFlatEarned
import YM.Integration.WilsonOriginalTwoFlatIRFlatPaidParts

/-! The absolute cost of dropping higher total grades from a complete
submitted finite-roster ordinary face on the moving flat. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatCapturedSale
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

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

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Filter MintClock Multi
local notation "H" => Ψ (i+1)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))


open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Soil FundedMarkedPathSelection WilsonOlderFreshConnectedRobe
open WilsonOriginalCollarElection WilsonIndependentCollarCensusCourse WilsonReceivedCanonicalVerseBasis
open WilsonThermometerDeclaredSeeds WilsonReceivedFixedDigitHistory WilsonIndependentCollarAddressedSource
open WilsonOriginalCensusDatedMaterial (Material)
open WilsonOriginalCensusFaceSites (binder port)
open Pert.Asymptotics
open WilsonOriginalTwoFlatIRFlatEarned (whole)
open WilsonOriginalTwoFlatIRFlatMarked (seat)
open WilsonOriginalTwoFlatIRFlatPaidParts (wage)
open WilsonOriginalTwoFlatIRFlatPartitions (crop)
open WilsonOriginalTwoFlatIRFlatMeasured (cash)
open WilsonReceivedChronologicalMaterialEndpoint (submitted)

variable {n K c q:ℕ}(grades axis:Fin n→ℕ){V:Realm G (q+1) Credit.leanC}{draw:V.draws=R.family.path.levels}
  {rate δ:ℝ}(κ:(v:Fin n)→Knob (axis v))(pt:Fin n→WilsonCoeffUV.Embroider.Chamber)(cells:Digits V.draws (Fin n))
  (seed:(v:Fin n)→Choice R grades v)(y:Fin n → Cover)(t:WilsonCoeffUV.Wheel.Case axis)
local notation "day" => i+1
local notation "g" => regulatorRun R.family N per (day)
local notation "side" => R.family.side (day) per
local notation "P₀" => port (side) y
local notation "B₀" => binder (side) y
local notation "J" => Stock.census (Fin n)
local notation "seats" => Hot (J)
local notation "Mtype" => Material R N (day) q grades (σ₀) (B₀)
local notation "D₀" => (∑v:Fin n,grades v)+1
local notation "room" => WilsonOriginalMixedBlockRows.room (Fin n)
local notation "target" => whole (R:=R) (N:=N) (K:=K) (c:=c) (j:=i) (draw:=draw) κ pt cells seed y t
local notation "cost" M:max x:max => wage (R:=R) (D:=D) (passport:=P₀) (B:=B₀) (grades:=grades) (q:=q) M x
local notation "file" M:max x:max => submitted R D Ψ (P₀) (B₀) grades q M x

include simple course cut hospital cal chamber in
theorem original (vc:day≤c)(ck:c≤K)(kn:K≤N)
    (funded:Submitted R V draw axis grades N K i rate δ (σ₀))
    (occupiedGrades:∀z:seats,0 < mass grades ((B₀) z).mode.val)
    (order shelf:ℕ)(H₀:Fin n→ℝ)
    (qfit:q ≤ order) (occupied:1 ≤ op.count)
    (size:∀v,0 < H₀ v) (slots:Fintype.card (Fin n) ≤ op.count) (count:op.count ≤ Burn.horizon k+2)
    (fit:(∑v,grades v) ≤ shelf) (level:shelf ≤ R.alloy.B.a.clock.J i) (stage:order+1 ≤ op.stage)
    (expense:order+(∑v,grades v) ≤ Burn.horizon k+2)
    {tol:ℝ} (tp:0 < tol) (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
    (atBare:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (pass:Pass D Q R.alloy R.kit)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ i+1)
    (onset:WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ)) ≤ i)
    (p:ℕ) (way:WayStation R.kit) (hardFloor:6*op.count ≤ R.alloy.B.a.clock.J i)
    (deep:2*(p+1)+8 ≤ order)(aged:p+4 ≤ 3*k+2)
    (opened:WilsonFirstReceivedEarnedFee.opening R simple op.count p order k deep aged
      (by norm_num:0<(1:ℝ)) ≤ i)
    (more:WilsonMeasuredSemesterSubpower.onset R op.count (by norm_num:0<(1:ℝ)) ≤ i)
    (cooled:(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ i+1)
    (fresh:(eventually_atTop.mp (WilsonOriginalOccupiedModeFactors.original R simple
      (Fintype.card (Fin n)) (order+shelf+1+(D₀)) ((D₀)+2))).choose ≤ i)
    (hg:0≤g)(small:g≤1):
    ∃M:Mtype,M.realm=V ∧ M.tests=axis ∧ M.amplitude=rate ∧ M.allowance=δ ∧
      WilsonOriginalCensusMaterialPosting.Posted R hk D Q π Γ Ψ books hi op lesson ahead
        (P₀) (B₀) grades order shelf q H₀ M tol ∧
      (∀(x:Fin n→ℂ)(θ:ℂ)(a:ℕ),a≤q→∀(S:Finset (Fin n)),
        (crop (fun z:seats=>((B₀) z).mode) (cash M x) θ a).part (seat S)=(target) x θ a S) ∧
      ∀(x:Wallet (room))(p':ℕ),p'≤q→∀(S:Finset (Fin n)),
        ‖((R.family.path.rep N per (day)).eval 1:ℂ)⁻¹*((file M x) 1).part (seat S)-
            (target) (fun v=>(x v).val) g p' S‖≤g^(p'+1)*∏z:seats,(1+(cost M x) z):=by
  obtain ⟨M,realm,axes,gross,rent,_holds,_paths,matched⟩:=
    WilsonOriginalTwoFlatIRFlatEarned.original κ pt cells seed y t simple vc ck kn funded (side) occupiedGrades
  have paid:=WilsonOriginalCensusMaterialPosting.original R simple hk D Q π Γ Ψ course scroll books hi cut
    op lesson cal ahead chamber hospital (P₀) (B₀) grades order shelf q H₀ M qfit occupied size slots count
    fit level stage expense tp warm atBare pass halo onset p way hardFloor deep aged opened more cooled fresh
  refine ⟨M,realm,axes,gross,rent,paid,matched,?_⟩
  intro x p' floor S
  obtain ⟨_,_,_,_,measured⟩:=WilsonOriginalTwoFlatIRFlatPosted.original R hk D Q π Γ Ψ course books hi cut
    op lesson ahead (P₀) (B₀) grades order shelf q H₀ M tol paid x
  rw [measured]
  have sold:=WilsonOriginalTwoFlatIRFlatPaidParts.original R D (P₀) (B₀) grades q M x g hg small p' (seat S)
  rw [←matched (fun v=>(x v).val) g p' floor S]
  exact sold

end YM.Integration.WilsonOriginalTwoFlatIRFlatCapturedSale
end
