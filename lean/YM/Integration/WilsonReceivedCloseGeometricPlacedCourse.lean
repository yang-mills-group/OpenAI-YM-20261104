import YM.Integration.WilsonReceivedGeometricPlacedHard
import YM.Integration.WilsonReceivedCloseGeometricHardCourse
import YM.Integration.WilsonReceivedCloseGeometricPriorCourse

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseGeometricPlacedCourse
open Filter Finset Multi Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior Comparison.RG02.Cumulants
open OPE.Therm WilsonLimitConstruction RG16.Literal Source Labels Extra.Histories
open scoped BigOperators Classical

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {X : Fin 3 → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : Fin 3 → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census (Fin 3)))

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per


local notation "J₀" => Stock.census (Fin 3)
local notation "Pupil" i:max mi:max L:max =>
  Oak.student (n:=per) (i:=i) R hk D Q π Γ books mi (L).op (L).lesson ahead actors (L).model order (L).voter
local notation "teacher" i:max mi:max L:max x:max => Air.craft (Pupil i mi L)
  (fun s=>((Pupil i mi L) s).paint x) grades (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "bank" i:max L:max x:max => Air.craft (L).model (fun s=>((L).model s).paint x)
  grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "Covered" => ∀i:ℕ,i ≤ b → Wallet actors → Stationary.Link G (R.family.side i per) → ℕ → Poly J₀
local notation "Walk" start:max i:max mi:max ib:max L:max =>
  WilsonReceivedCloseHistory.Trail (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    mb source start i mi (read i ib) L


local notation "charge" i:max mi:max L:max =>
  (8*(Oak.expenseReal (i:=i) R hk D Q π Γ books mi (L).op (L).lesson ahead order shelf)^(L).op.count)*(L).rent
local notation "p" a:max d:max q:max => q+1+(d*a+1)+a

local notation "homes" i:max L:max => ((L).passport.coarser (move i).ratio).origin

open WilsonMeasuredCoefficientTransport Trace.Physical
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "Rough" => |WilsonFullFaceSignedPower.constants (S₀) (R.family.params) 100 ((2:ℝ)^(order+shelf+2)+4)|
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

/-- The reference at the previous date and each housed original signed scalar use
the same enrolled history, original prior and genuine compulsory account. -/
def Repaid (start:P b mb source) (K:Covered) (singer:MSbar.Heath.Voice G) (axes:Lattice.Order)
    (d q target sourcePower:ℕ) (ε wallet:ℝ) : Prop :=
  ∀ i (ib:i+1 ≤ b) (mi:m ≤ i),∃ (L:P (i+1) (mi.trans (Nat.le_succ i)) (read (i+1) ib))
    (lower:P i mi (read i (Nat.le_trans (Nat.le_succ i) ib))),
    Walk start (i+1) (mi.trans (Nat.le_succ i)) ib L ∧
    Walk start i mi (Nat.le_trans (Nat.le_succ i) ib) lower ∧
    (∀s:(J₀).Mode,(g (i+1+1))^(d*s.val.card+1) ≤ Poly.toll L.w s) ∧
    ∀ (fired:Wallet actors) (c:(J₀).Mode → ℂ) (y:Site (R.family.side (i+1) per)) (Z:Support (R.family.side (i+1) per)),
      y∈Z → (∀v,(homes (i+1) L) v∈Z) → 
      ∀ rad:ℕ,(∀v,separation ((homes (i+1) L) v) y ≤ rad) → rad ≤ (Ψ (i+1)).p.B → Z⊆halo (Ψ (i+1)).p.B {y} → 
      (g (i+1+1))^sourcePower*(∑s,‖c s‖) ≤ wallet → 
      ∃ heard:WilsonReceivedGeometricCoveredPrior.Heard R hk D Q π Γ Ψ books (mi.trans (Nat.le_succ i)) ahead
        order shelf seats actors pieces grades (read (i+1) ib) L fired singer axes q target sourcePower d ε wallet c y (K (i+1) ib),
      let h:=Classical.choose heard
      ∃ (z:Coefficient (F₀) (R.family.side i per)) (u:ℝ),
        (z.Format ((R.family.path.levels.clock.op i per).ratio.parent y) R.family.params (Ψ i) ∧ z.remBound ((R.family.path.levels.clock.op i per).ratio.parent y) (Ψ i) (κ i) u) ∧ (F₀).coeffSize z.x ≤ u ∧
        GermGraph.transition (C:=R.family) 0 N per i (account h (Ψ (i+1))) = z.density ((R.family.path.levels.clock.op i per).ratio.parent y) (S₀) (Ψ i) ∧
        (2+4*(R.family.path.levels.params i).columns)*u ≤ 
          ((R.family.S.block i).val:ℝ)^(-(1/8:ℝ))*(Rough*wallet*(2+4^q)*(g (i+1+1))^(target+1))

section
variable (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
    (lamp:WilsonReportLampForecast.Ready R.family.path.levels)
    (deep:2*(5+4+1)+8 ≤ order) (aged:5+4+4 ≤ 3*k+2)

open WilsonReceivedCloseGeometricHardCourse in
theorem original (start:P b mb source) (K:Covered) (singer:MSbar.Heath.Voice G) (axes:Lattice.Order)
    (d q target sourcePower:ℕ) (ε wallet:ℝ)
    (served:WilsonReceivedCloseGeometricPriorCourse.Served R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source start K singer axes d q target sourcePower ε wallet)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (top:b<N)
    (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (pass:Pass D Q R.alloy R.kit) (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (load:seats ≤ Burn.horizon k+2) (way:WayStation R.kit)
    {σ:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (funded:FundedOriginalProperties.{u} simple σ W)
    (booked:Booked R order shelf simple slow lamp deep aged m) :
    Repaid R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source
      start K singer axes d q target sourcePower ε wallet := by
  obtain ⟨M,scheduled⟩:=booked
  intro i ib mi
  have lo:= (Nat.le_succ i).trans ib
  have hi:=mi.trans (Nat.le_succ i)
  obtain ⟨L,walk,sale,upper⟩:=served (i+1) ib hi
  obtain ⟨lower,path,_,_⟩:=served i lo mi
  refine ⟨L,lower,walk,path,sale,?_⟩
  intro fired c y Z root rows rad near size inBox price
  have heard:=upper fired c y Z root rows rad near size inBox price
  refine ⟨heard,?_⟩
  have raw:P i mi (fun test=>LocalComparison.actualPush R.family N per (i+1) ((read (i+1) ib) test)) := by
    rw [WilsonReceivedCloseHistory.adjacent R actors source ib]
    exact lower
  exact WilsonReceivedGeometricPlacedHard.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    mi (read (i+1) ib) L raw (lo.trans_lt top) simple course scroll chamber pass hospital load way
    M slow.2 lamp funded deep aged (scheduled i mi) y fired singer axes q target sourcePower d ε wallet c (K (i+1) ib) heard
end
end YM.Integration.WilsonReceivedCloseGeometricPlacedCourse
