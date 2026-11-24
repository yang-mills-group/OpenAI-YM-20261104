import YM.Integration.WilsonReceivedCloseStationCalendar

/-! The true signed, unweighted ordinary panel throughout the enrolled Wilson close range. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseRefundedWindow
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior Comparison.RG02.Cumulants
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per




variable (P₀:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats b mb source) (simple:G.Simple) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (path:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (top:b<N)
  (pass:Pass D Q R.alloy R.kit) (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
  (month:Scholar.Month R.rolls D Q R.alloy.delay)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (volume:Volume.Fund D R.rolls Q φ books R.alloy.delay)
  (protection:∀ x k:ℕ,k≤x→∀β:ℝ,R.alloy.delay.betaEntry x≤β→
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2)≤β)
  (fits:order ≤ Burn.horizon k+1) (thin:shelf ≤ R.alloy.B.a.clock.J m)
  (load:seats ≤ Burn.horizon k+2) (packed:order+shelf ≤ Burn.horizon k+2)
  (stage:k ≤ R.alloy.B.a.clock.J m) (test:Wallet actors)
  (a d q prec span degree:ℕ) (u H angleCap cap ε:ℝ) (u1:1≤u)
  (deep:2*(prec+1)+8≤order) (aged:prec+4≤3*k+2) (hp:0≤angleCap) (cp:0≤cap) (ep:0<ε)
local notation "days" => WilsonReceivedCloseStationCalendar.Ready R simple D φ protection grades k order shelf seats
  a d q prec span degree u H angleCap cap ε u1 deep aged hp cp ep m b
local notation "pages" => WilsonReceivedCloseSlate.opens R D grades order shelf seats simple protection prec span deep aged
  H angleCap hp zero_lt_one

include course path pass scroll chamber month hospital volume protection fits thin load packed stage test in
theorem original (closeDates:PaceR.Close R degree cap m b)
    (reserve:2*d*a+(q+(2*d+1)*a+1+a)+3≤prec) (orderFits:a+(q+(2*d+1)*a+1)≤order+1)
    (calendar:days) (birth:∀v,(P₀.w v)⁻¹≤u*((g b)⁻¹)^(2*d)) (rent:P₀.rent≤(g b)^prec) :
    WilsonReceivedCloseNamedWallet.Sold R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
        source P₀ univ (u*((g b)⁻¹)^(2*d+1)) ∧
      WilsonReceivedCloseOrdinaryRoster.Served R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
        source P₀ top span H angleCap univ a (u*((g b)⁻¹)^(2*d+1)) ((g b)^(q+(2*d+1)*a+1+a)) (ε*(g b)^q) := by
  obtain ⟨openRead,late,paid,room,clock,band,cool,selected,earn,tested⟩:=calendar
  apply WilsonReceivedCloseStationedFaces.original R hk D Q π Γ Ψ books ahead actors pieces grades order
    shelf seats mb source P₀ top simple course stage protection scroll chamber volume a d q prec degree span
    cp u1 hp ep reserve orderFits birth rent closeDates room clock band cool selected earn tested
  exact WilsonReceivedCloseSlate.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
    source simple protection prec span deep aged H angleCap hp zero_lt_one P₀ course path top pass scroll chamber month
    hospital volume fits thin load packed le_rfl stage ((eventually_atTop.mp (pages)).choose_spec m openRead)
    late test degree a cp zero_lt_one paid closeDates

end YM.Integration.WilsonReceivedCloseRefundedWindow
