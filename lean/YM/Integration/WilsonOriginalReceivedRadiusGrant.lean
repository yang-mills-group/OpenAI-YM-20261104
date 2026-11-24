import YM.Integration.WilsonOriginalReceivedFirstMarkers
import YM.Integration.WilsonOriginalReceivedFiledReference
import YM.Integration.WilsonOriginalReceivedFirstEnrollment
import YM.Integration.WilsonOriginalReceivedFiledChain

/-! Charge the actual filed source and its two signed hard alternatives at the
radius at which the nearer Wilson block receives them. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedRadiusGrant
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity QuadraticLocal.Tint Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain


variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ j)
  (physical : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V))

  (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
    (floor.trans (Nat.le_succ j)) physical)

local notation "earlier" => (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x))
local notation "elected" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead order shelf
local notation "hi" => floor.trans (Nat.le_succ j)
variable [Countable P.inputIndex]
  (simple:G.Simple) (cut:j+1<N) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (load:P.op.count≤Burn.horizon k+2) (wide:shelf≤R.alloy.B.a.clock.J (j+1)) (test:Wallet actors)
local notation "initial" op:max => op R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
  (floor.trans (Nat.le_succ j)) physical P simple cut course scroll chamber hospital load wide test
local notation "issued" => initial WilsonOriginalReceivedFirstEnrollment.installed
local notation "coarsePost" => Post (N:=N) (V:=V) (X:=X) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor earlier
variable (L:WilsonOriginalReceivedChain.Post (N:=N) (V:=V) (X:=X) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x))) (filed:WilsonOriginalReceivedChain.Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
  (j:=j) floor physical (WilsonOriginalReceivedFirstEnrollment.installed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) physical P simple cut course scroll chamber hospital load wide test) L)
variable (h:ℝ) (full:1≤h) (width:∀a,L.w a=P.w a/(elected^6*h))
variable (funded:WilsonWindowOriginalHardRadius.Booked R.kit) (d:ℕ) (select:(Stock.census V).Mode→Prop)
  (v:V) (contains:∀t,select t→v∈t.val)
local notation "fine" => Ψ ((j+1)+1)
local notation "quote" => Time.quoteHard R.alloy.B.a (j+1) R.kit.book (fine).beta
local notation "delta" => (↑((Real.exp ((fine).p.supportExponent/8*d))⁻¹):ℂ)
local notation "markers" dist₀:max => WilsonOriginalReceivedFirstMarkers.terms R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) physical P simple cut course scroll chamber hospital load wide test funded d select v contains dist₀
local notation "charged" dist₀:max => WilsonOriginalReceivedFirstMarkers.width R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) physical P simple cut course scroll chamber hospital load wide test funded d select v contains dist₀
local notation "apart" => ∀t, select t→∃a∈t.val, ∃b∈t.val,
    d*(4*(fine).p.B+2)+2*(fine).p.B ≤ separation (P.passport.origin a) (P.passport.origin b)
local notation "sector" => Hard (Wallet actors) (Ψ (j+1)).p (Ψ (j+1)).activities.forced (Ψ (j+1)).activities.K
  L.passport.origin (Stock.census V)

local notation "originating" => Hard (Wallet actors) (Ψ (j+1)).p (Ψ (j+1)).activities.forced (Ψ (j+1)).activities.K
  ((Pane.panel R.alloy (j+1) (R.alloy.B.a.S.oneStep (j+1) per).exact_size).ratio.parent ∘ P.passport.origin) (Stock.census V)

omit [Countable P.inputIndex] in
private theorem salePositive : 0 < elected^6 := pow_pos (zero_lt_one.trans_le P.issued.Waffle.cool) 6

include full in
set_option backward.isDefEq.respectTransparency true in
theorem half (sp : 0 < elected^6) (ports : L.passport.origin = ((Pane.panel R.alloy (j+1) (R.alloy.B.a.S.oneStep (j+1) per).exact_size).ratio.parent ∘ P.passport.origin)) (ticket : HEq L.input.hard (WilsonOriginalReceivedFirstPost.hardAt R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) physical P simple cut course scroll chamber hospital load wide test)) (x y : originating) (at_source : WilsonOriginalForcedMarkerMerger.Related v delta x (WilsonOriginalReceivedFirstPost.hardAt R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) physical P simple cut course scroll chamber hospital load wide test) y) (covered : x.Paid (Stoop.radius P.w (elected^6)) (Ψ (j+1)).p.B (Ψ (j+1)).p.supportExponent quote ∧ y.Paid (Stoop.radius P.w (elected^6)) (Ψ (j+1)).p.B (Ψ (j+1)).p.supportExponent quote)  :
    (∀ a, L.w a=P.w a/(elected^6*h)) →
    ∃ (removed raised : sector), HEq removed x ∧ HEq raised y ∧
      removed.Paid L.w (Ψ (j+1)).p.B (Ψ (j+1)).p.supportExponent quote ∧
      raised.Paid L.w (Ψ (j+1)).p.B (Ψ (j+1)).p.supportExponent quote ∧
      WilsonOriginalForcedMarkerMerger.Related v delta removed L.input.hard raised :=
  WilsonOriginalReceivedFiledReference.paid_places (Ψ (j+1)).activities (v:=v) (mul:=delta) (w:=P.w) (next:=L.w)
    (sale:=elected^6) (h:=h) (B:=(Ψ (j+1)).p.B) (a:=(Ψ (j+1)).p.supportExponent) (c:=quote)
    (T:=Wallet actors) (M:=Stock.census V) (p:=(Ψ (j+1)).p) (newPos:=L.passport.origin)
    (oldPos:=((Pane.panel R.alloy (j+1) (R.alloy.B.a.S.oneStep (j+1) per).exact_size).ratio.parent ∘ P.passport.origin)) (held:=WilsonOriginalReceivedFirstPost.hardAt R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) physical P simple cut course scroll chamber hospital load wide test) (now:=L.input.hard) ports x y
    ticket at_source covered P.salary.positive
    sp full


end YM.Integration.WilsonOriginalReceivedRadiusGrant
end
