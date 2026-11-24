import YM.Integration.WilsonOriginalTwoFlatIRFlatCapturedSale
import YM.Integration.WilsonOriginalTwoFlatIRFlatChronicle
import YM.Integration.WilsonOriginalPublicFixedCourse

/-! One original terminal file for every actual signed K choice of the three named
sources. Its digits and roots are those of the original N-sites. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseFixedFiles
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


open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedCanonicalVerseWeighted (full)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonReceivedChronologicalBasis (fare)
open WilsonIndependentCollarDatedPrior (onLevels)
variable {f n cap q:ℕ}(grades axis:Fin 3→ℕ){V:Realm G (q+1) Credit.leanC}{draw:V.draws=R.family.path.levels}
    {rate δ:ℝ}(κ:(v:Fin 3)→Knob (axis v))(pt:Fin 3→WilsonCoeffUV.Embroider.Chamber)
    (o:Fin 3→Site (R.family.side f per))(upper:f+n≤N)(t:WilsonCoeffUV.Wheel.Case axis)
local notation "J" => Stock.census (Fin 3)
local notation "day" => i+1
local notation "g" => regulatorRun R.family N per (day)
local notation "side" => R.family.side (day) per
local notation "seats" => Hot (J)
local notation "D₀" => (∑v:Fin 3,grades v)+1
local notation "room" => WilsonOriginalMixedBlockRows.room (Fin 3)
local notation "top" => f+n
local notation "high" => (Nat.le_add_right f n).trans upper
local notation "sitesN" => pin R (high) o

private def anchor (s:(J).Mode):Fin 3:=if h:s.val.Nonempty then h.choose else 0

def site (h:i+1≤N)(s:(J).Mode):Fin 3 → Cover:=
  WilsonOriginalPublicFixedCourse.home R per (day) h (sitesN) (anchor s)

def cells:Digits V.draws (Fin 3):=onLevels draw.symm (WilsonOriginalPublicFixedCourse.digits R per (sitesN))

private theorem transport {G':Gauge}{L L':RG.Levels G'}(h:L=L')(x:Digits L' (Fin 3)):
    onLevels h (onLevels h.symm x)=x:=by subst L';rfl

theorem true_children (m:ℕ)(hm:m<N)(s:(J).Mode)(v:Fin 3):
    wrap (R.family.side (m+1) per) ((R.family.S.oneStep m per).count.val •
      (WilsonOriginalPublicFixedCourse.home R per m hm.le (sitesN) (anchor s) v)+
      lift (onLevels draw (cells R (draw:=draw) o upper) m v))=
    WilsonOriginalPublicFixedCourse.sites R per (m+1) hm (sitesN) v:=by
  rw [cells,transport]
  exact WilsonOriginalPublicFixedCourse.located R per m hm (sitesN) (anchor s) v

local notation "home" s:max => site R o upper cut s
local notation "B_" s:max => binder (side) (home s)
local notation "P_" s:max => port (side) (home s)
local notation "M_" s:max => Material R N (day) q grades (σ₀) (B_ s)
local notation "path" => cells R (draw:=draw) o upper

def retained (x:∀(s:(J).Mode)(_y:Selection R grades s.val),Wallet (room))
    (v:∀a:Fin 3,R.family.label (grades a))(c:Fin 3→ℂ)(p:ℕ)(s:(J).Mode):ℂ:=
  ∑y:Selection R grades s.val,fare R grades v c N per (top) s y *
    whole (R:=R) (N:=N) (K:=top) (c:=cap) (j:=i) (draw:=draw) κ pt (path) (full R grades y)
      (home s) t (fun a=>(x s y a).val) g p s.val


include simple course cut hospital cal chamber in
theorem original (vc:day≤cap)(ck:cap≤top)
    (funded:Submitted R V draw axis grades N (top) i rate δ (σ₀))
    (positive:∀v,0<grades v)
    (order shelf:ℕ)(H₀:Fin 3→ℝ)
    (qfit:q ≤ order) (occupied:1 ≤ op.count)
    (size:∀v,0 < H₀ v) (slots:Fintype.card (Fin 3) ≤ op.count) (count:op.count ≤ Burn.horizon k+2)
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
      (Fintype.card (Fin 3)) (order+shelf+1+(D₀)) ((D₀)+2))).choose ≤ i)
    (hg:0≤g)(small:g≤1):
    ∃M:∀(s:(J).Mode)(_y:Selection R grades s.val),M_ s,
      (∀s y, (M s y).realm=V ∧ (M s y).tests=axis ∧ (M s y).amplitude=rate ∧ (M s y).allowance=δ) ∧
      (∀s y,WilsonOriginalCensusMaterialPosting.Posted R hk D Q π Γ Ψ books hi op lesson ahead
        (P_ s) (B_ s) grades order shelf q H₀ (M s y) tol) ∧
      ∀(x:∀(s:(J).Mode)(_y:Selection R grades s.val),Wallet (room))
        (v:∀a:Fin 3,R.family.label (grades a))(c:Fin 3→ℂ)(p':ℕ),p'≤q→∀(s:(J).Mode),
        WilsonOriginalTwoFlatIRFlatChronicle.total R D (f:=f) (n:=n) grades v c
          (fun s _=>P_ s) (fun s _=>B_ s) q M x p' s =
        retained R (cap:=cap) (draw:=draw) cut grades axis κ pt o upper t x v c p' s:=by
  have each (s:(J).Mode)(y:Selection R grades s.val):=by
    have pos (z:seats):0 < mass grades ((B_ s) z).mode.val:=by
      change 0<∑a∈z.val.val,grades a
      obtain ⟨a,ha⟩:=z.property
      exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨a,ha,positive a⟩
    exact WilsonOriginalTwoFlatIRFlatCapturedSale.original R simple hk D Q π Γ Ψ course scroll books hi cut
      op lesson cal ahead chamber hospital grades axis κ pt (path) (full R grades y) (home s) t vc ck upper
      funded pos order shelf H₀ qfit occupied size slots count fit level stage expense tp warm atBare pass
      halo onset p way hardFloor deep aged opened more cooled fresh hg small
  choose M realm axes amplitude allowance paid selected _fees using each
  refine ⟨M,fun s y=>⟨realm s y,axes s y,amplitude s y,allowance s y⟩,paid,?_⟩
  intro x v c p' booked s
  apply Finset.sum_congr rfl
  intro y _
  apply congrArg (fare R grades v c N per (top) s y * ·)
  exact selected s y (fun a=>(x s y a).val) g p' booked s.val

end YM.Integration.WilsonOriginalTwoFlatRoseFixedFiles
end
