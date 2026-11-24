import YM.Integration.WilsonOlderSignedOneMarkAveraged
import YM.Integration.ActualScalarTransport

/-! Signed telescoping of freshly planted group words on the original finite Wilson history. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkScalarChain
open MeasureTheory OPE.Therm
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org 
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))

local notation "post" F:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades order shelf seats i floor F
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades order shelf seats i floor physical)
local instance : Countable P.modelIndex := P.modelCount
local notation "fine" => Ψ (i+1)
local notation "gf" => Coat.gStep (fine).beta
local notation "κ" => forcedDivisor R.family (i+1)
local notation "βhat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "fresh" => (fun (x : Wallet actors) (U : Config G (R.family.side (i+1) per)) =>
  ((fine).eval U : ℂ) • Poly.pass (Spill.Foundry.uncut P.model gf x U))
local notation "pupil" S:max => Oak.student (n:=per) R hk D Q π Γ books floor (S).op (S).lesson ahead
  actors (S).model order (S).voter


include course in
theorem row (cut : i<N) (scroll : VowsR.LawScroll G φ)
    (chamber : VowsR.Chamber scroll R.kit D Q books)
    (warm : Spill.Raffle.Warm G D R.alloy.delay φ)
    (top : Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (fits : order ≤ Burn.horizon k+1) (load : seats ≤ Burn.horizon k+2)
    (packed : order+shelf ≤ Burn.horizon k+2)
    (d : ℕ) (space : Sycamore.Boot.need d (⟨order,seats,shelf,load,fits,packed⟩ : Syl.School k)
      ≤ R.alloy.B.a.clock.J (i+1))
    (x : Wallet actors) (v : V) :
    Integrable (fun U=>(R.family.path.rep N per (i+1)).eval U •
      (Spill.Foundry.uncut P.model gf x U).part ((Stock.census V).fire v)) (prior G _) := by

  have live := WilsonOlderSignedOneMarkAdmitted.original R hk D Q π Γ Ψ course books ahead actors
    pieces grades order shelf seats floor physical P cut scroll chamber warm top fits load packed d space x
  have paid := (Poly.get ((Stock.census V).fire v)).integrable_comp live
  have original : (fine).eval=(R.family.path.rep N per (i+1)).eval :=
    (course.1.walk (i+1) (floor.trans (Nat.le_succ _)) cut).view
  apply paid.congr
  filter_upwards [] with U
  change ((↑((fine).eval U):ℂ) • Poly.pass (Spill.Foundry.uncut P.model gf x U)).part
    ((Stock.census V).fire v) = _
  rw [WilsonOlderFreshWordReversion.singleton,original,Complex.real_smul]

variable (C : Family G) (law : C.Makes) {u b : ℕ}
local notation "Y" i:max => Config G (C.side i per)
local notation "μ" i:max => scene C.path N per i

include law in
theorem telescope (start : u≤b) (cap : b≤N) (fields : ∀ j,Y j → ℂ)
    (paid : ∀ j, u≤j → j≤b →
      Integrable (fun W=>(C.path.rep N per j).eval W • fields j W) (prior G _)) :
    (∫ W,fields b W ∂μ b)-(∫ W,fields u W ∂μ u) =
      ∑ j∈Ico u b,∫ W,actualAverage C (N:=N) (fields (j+1)) W-fields j W ∂μ j := by
  let E:=fun j=>(∫ W,fields j W ∂μ j)
  have step (j : ℕ) (uj : u≤j) (jb : j<b) :
      (∫ W,actualAverage C (N:=N) (fields (j+1)) W-fields j W ∂μ j)=E (j+1)-E j := by
    have diff:=actualScene_step_error C law (jb.trans_le cap) (paid j uj jb.le)
      (paid (j+1) (uj.trans (Nat.le_succ j)) jb)
    have neg : (fun W=>actualAverage C (N:=N) (fields (j+1)) W-fields j W)=
        (fun W=> -(fields j W-actualAverage C (N:=N) (fields (j+1)) W)) := by
      funext W
      abel
    rw [neg,integral_neg,diff]
    dsimp only [E]
    abel
  have ends (t : ℕ) (ut : u≤t) : (∑ j∈Ico u t,(E (j+1)-E j))=E t-E u := by
    induction t,ut using Nat.le_induction with
    | base=>simp
    | succ j uj ih=>rw [sum_Ico_succ_top uj,ih]; abel
  change E b-E u=_
  rw [←ends b start]
  apply sum_congr rfl
  intro j hj
  exact (step j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2).symm

end YM.Integration.WilsonOlderSignedOneMarkScalarChain
