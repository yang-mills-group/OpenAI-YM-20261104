import YM.Integration.WilsonOriginalReceivedFirstMarkers
import YM.Integration.WilsonOriginalReceivedFirstEnrollment
import YM.Integration.WilsonOriginalReceivedFiledChain

/-! Charge the actual filed source and its two signed hard alternatives at the
radius at which the nearer Wilson block receives them. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedFiledReference
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity QuadraticLocal.Tint Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain

section Positions
open Function Filter Ac QuadraticLocal.Fusion QuadraticLocal.Canopy QuadraticLocal.Fusion.Attached RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe
variable {G:Gauge} {n:Side} {p:BudgetPoint} {V T : Type} [DecidableEq V] {M : Marker.Census V}
  {oldPos newPos:V→Site n} {F:ℕ→ForcedAddress G n} {K:Code G n}
local notation "HardAt" origin:max => Hard T p F K origin M

def place (same : newPos=oldPos) (item:HardAt oldPos) : HardAt newPos := same.symm ▸ item

theorem placed (same:newPos=oldPos) (item:HardAt oldPos) : HEq (place same item) item := by
  cases same
  rfl

theorem receipt [Fintype V] (same:newPos=oldPos) (item:HardAt oldPos) {w:V→ℝ} {B:ℕ} {a c:ℝ}
    (paid:item.Paid w B a c) : (place same item).Paid w B a c := by
  cases same
  exact paid

theorem balance (same:newPos=oldPos) {a b c:HardAt oldPos} {now:HardAt newPos} {v:V} {delta:ℂ}
    (measured:HEq now b) (old:WilsonOriginalForcedMarkerMerger.Related v delta a b c) :
    WilsonOriginalForcedMarkerMerger.Related v delta (place same a) now (place same c) := by
  cases same
  rw [eq_of_heq measured]
  exact old

omit [DecidableEq V] in
private theorem radius (w next : V→ℝ) (sale h:ℝ) (wages:∀u,next u=w u/(sale*h)) :
    next = Stoop.radius (Stoop.radius w sale) h := by
  funext t
  exact (wages t).trans (div_div _ _ _).symm

theorem paid_places [Fintype V] (stock : Activities G n) (same:newPos=oldPos) (x y:Hard T p stock.forced stock.K oldPos M) {held:Hard T p stock.forced stock.K oldPos M}
    {now:Hard T p stock.forced stock.K newPos M} {v:V} {mul:ℂ} {w next:V→ℝ} {sale h:ℝ} {B:ℕ} {a c:ℝ}
    (meeting:HEq now held) (old:WilsonOriginalForcedMarkerMerger.Related v mul x held y)
    (hard:x.Paid (Stoop.radius w sale) B a c ∧ y.Paid (Stoop.radius w sale) B a c)
    (pos:∀u,0<w u) (sp:0<sale) (one:1≤h) (wages:∀u,next u=w u/(sale*h)):
    ∃ (x' y':Hard T p stock.forced stock.K newPos M), HEq x' x ∧ HEq y' y ∧ x'.Paid next B a c ∧ y'.Paid next B a c ∧
      WilsonOriginalForcedMarkerMerger.Related v mul x' now y' := by
  cases same
  have size:=radius w next sale h wages
  have trueK:=eq_of_heq meeting
  have wp:∀u,0<(Stoop.radius w sale) u := fun u => div_pos (pos u) sp
  refine ⟨x,y,HEq.rfl,HEq.rfl,?_,?_,?_⟩
  · rw [size]
    exact Stoop.leaves (X:=stock) _ x wp one hard.1
  · rw [size]
    exact Stoop.leaves (X:=stock) _ y wp one hard.2
  · rw [trueK]
    exact old

end Positions
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

include filed in
theorem origins : L.passport.origin = ((P.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio)).origin := by
  exact congrArg (fun K : Earn.Passport (R.family.side (j+1) per) V => K.origin) filed.passport

include filed in
theorem hard_filed : HEq L.input.hard (WilsonOriginalReceivedFirstPost.hardAt R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) physical P simple cut course scroll chamber hospital load wide test) := by
  have shifted := WilsonOriginalReceivedFirstEnrollment.selected R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) physical P simple cut course scroll chamber hospital load wide test
  exact filed.hard.trans (heq_of_eq shifted)

end YM.Integration.WilsonOriginalReceivedFiledReference
end
