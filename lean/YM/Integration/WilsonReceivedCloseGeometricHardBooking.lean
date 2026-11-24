import YM.Integration.WilsonReceivedCloseGeometricHardCourse

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseGeometricHardBooking
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
  (order shelf : ℕ) (mb : m ≤ b)

def Entitled : Prop :=
  ∀ {X : Fin 3 → Type} [∀v, AddCommGroup (X v)] [∀v,Module ℝ (X v)]
    (actors:∀v,Set (X v)) (pieces:∀v,Submodule ℝ (X v)) (grades:Fin 3 → ℕ)
    (seats:ℕ), seats ≤ Burn.horizon k+2 →
    ∀ (source:Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census (Fin 3)))
      (start:Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats b mb source)
      (K:∀ i,i ≤ b → Wallet actors → Stationary.Link G (R.family.side i per) → ℕ → Poly (Stock.census (Fin 3)))
      (singer:MSbar.Heath.Voice G) (axes:Lattice.Order) (d q target sourcePower:ℕ) (ε wallet:ℝ),
      WilsonReceivedCloseGeometricPriorCourse.Served R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
        mb source start K singer axes d q target sourcePower ε wallet →
      WilsonReceivedCloseGeometricHardCourse.Repaid R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
        mb source start K singer axes d q target sourcePower ε wallet

theorem original (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
    (lamp:WilsonReportLampForecast.Ready R.family.path.levels)
    (deep:2*(5+4+1)+8 ≤ order) (aged:5+4+4 ≤ 3*k+2)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (top:b<N)
    (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (pass:Pass D Q R.alloy R.kit) (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (way:WayStation R.kit) {σ:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (funded:FundedOriginalProperties.{u} simple σ W)
    (booked:WilsonReceivedCloseGeometricHardCourse.Booked R order shelf simple slow lamp deep aged m) :
    Entitled (N:=N) R hk D Q π Γ Ψ books ahead order shelf mb := by
  intro X _ _ actors pieces grades seats load source start K singer axes d q target sourcePower ε wallet served
  exact WilsonReceivedCloseGeometricHardCourse.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    mb source simple slow lamp deep aged start K singer axes d q target sourcePower ε wallet served course top
    scroll chamber pass hospital load way funded booked

end YM.Integration.WilsonReceivedCloseGeometricHardBooking
