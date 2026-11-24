import YM.QuadraticLocal.Neighborhood.UvPath

/-!
# Propagation of marked data across a finite interval

`Orbit.Licence` records bounds on the extent at each level and the available
orders at the ends of an interval `[m,b]`. Its `buds` field applies to a
supplied `Concourse` with terminal `Topline` data. The finite census, its
parent-compatible addresses and supports, its positive weights, and the
occupancy bound are among the inputs.

There are two ways to start at `b`. For a countable family of lamps with
`Affinity.Taut`, `RootsE` and `Origin.Global`, the licence supplies a hard
packet, the votes along the interval, and the identity for the density at
`b`. For a supplied estate with `Affinity.Collared`, `RootsE` and `RootsK`,
it supplies the votes for that estate.

Given the comparison data, warmth and quantity bounds in its hypotheses,
`Orbit.arena` obtains `Boot.Alumni` and this licence on every qualifying
interval with sufficiently large upper level `b`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces
open Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
open Extra.Histories
variable {G: Gauge} (R:Run G) (g : G.Simple)
local notation "S"=> R.alloy.B.a
local notation "Ta"=> R.T
local notation "Sz"=> R.metals.p
local notation "A"=> R.alloy
local notation "F"=> R.kit
local notation "Z"=> R.family
local notation "c"=> R.family.side
variable {m n i b q k N:ℕ} (h:WayStation R.kit) (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
set_option quotPrecheck false
local notation "ρ"=> Burn.horizon k
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "τ"=> R.alloy.B.a.clock.op i n
local notation "Y"=> R.alloy.B.a.clock.J (i+1)
local notation "I"=> R.alloy.B.a.clock.J i
local notation "L"=> R.rolls.L Y
local notation "X"=> R.alloy.B.a.budget i
local notation "W"=> R.alloy.B.a.budget (i+1)
local notation "xd"=> Φ i
local notation "γ"=> Φ (i+1)
local notation "Vd"=> (Φ i)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (K₀:TicketP R.alloy R.kit D Q)
variable (l:m≤ i)
local notation "P"=> Ψ (i+1)
local notation "P↓"=> Ψ i
local notation "H"=> Opera.Guide R.alloy.B (R.kit.shape)
local notation "wa"=> Time.forecastK S i (R.kit).scout (P).beta
local notation "wp"=> Time.quoteHard S i (R.kit).book (P).beta
local notation "y₀"=> Willow.haloSlack (X).B
local notation "Γ'"=> R.T.history N n
open Integration.LocalComparison
open Marker
namespace Sycamore
set_option quotPrecheck false
local notation "Φd"=> Φ b
local notation "Op'"=> R.family.path.levels.clock.op i n
namespace Moonlight
open Coat Travel PaceR VowsR Affinity MintClock Mentor Pavilion
variable {θ I₁:Type} [DecidableEq θ][Fintype θ] {J:Marker.Census θ}
variable {φ:ℕ→ℕ}(C:VowsR.LawScroll G φ)(Q0:QuadraticLocal.Mentor.Offices.Books D R.rolls Q φ)
variable (Pt:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
variable (Uq:Pavilion.Purchased D R.rolls Q R.kit.target φ Q0 R.alloy.delay)
variable (hv:VowsR.Chamber C R.kit D Q Q0)
local notation "salary"=> Q0.salary Y I Pt
local notation "μΖ"=> salary.price
local notation "ωΖ"=> salary.enroll
local notation "κP"=> Pavilion.Degree D R.rolls Q (R.kit).target φ Q0 (A).delay Pt Uq
local notation "tΩ"=> Delay.fineMonitor G L
local notation "Ω"=> (Delay.fineMonitor G L xd)^κP
namespace Orbit
variable (Qa: Mentor.Forecast D R.rolls Q φ Q0)(Yq:Oak.Tutoring.Quarterly R D Q C Q0 Qa)
variable (Z': Syl.School k)
variable (D0: Curriculum R)
open QuadraticLocal.Neighborhood QuadraticLocal.Neighborhood.Aperture QuadraticLocal.Neighborhood.Origin Quantity
variable (HP:Quantity.Park R.rolls R.alloy.delay)
variable (hw':Spill.Raffle.Warm G D R.alloy.delay φ)
variable (δ ℓspan:ℝ)
local notation "wB" w:max i:max => Stoop.radius w (extent R D Q Q0 Uq D0 i b)
local notation "Yr"=> Boot.Alumni
structure Licence (q qV M1 m b:ℕ) (ε:ℝ) : Prop where
     spending : ∀ i, m≤ i→i≤ b→ (extent R D Q Q0 Uq D0 i b)^M1 ≤ ( R.alloy.B.a.clock.hatBeta b)^ε ∧ extent R D Q Q0 Uq D0 i b ≤ Beaming.spray ( R.alloy.B.a.clock.hatBeta b )^(b-i)
     level : q+1≤ R.alloy.B.a.clock.J m ∧ qV ≤ R.alloy.B.a.clock.J b
     buds (N n:ℕ)(hN:b≤N)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n)) (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ) (hP:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N)) : ∀ (θ':Type) [Fintype θ'][DecidableEq θ'](J:Marker.Census θ') (X':θ'→Type)[∀ i,AddCommGroup (X' i)][∀ i,Module ℝ (X' i)] (Actors:∀ i,Set (X' i))[Nonempty (Affinity.Wallet Actors)](uK:∀ i, Submodule ℝ (X' i)) (o:(j:ℕ)→θ'→Site (R.family.side j n))(Loc:(j:ℕ)→θ'→Support (R.family.side j n)), (∀ i,m≤ i→i<b → o i= (R.family.path.levels.clock.op i n).ratio.parent ∘ o (i+1))→(∀ i,m≤ i→i<b → Loc i=(fun j=> (Loc (i+1) j).image (R.family.path.levels.clock.op i n).ratio.parent))→ ∀ w : θ' →ℝ, (∀ i,0<w i) → ∀ (e:ℝ)(k₁:ℕ),0<e→e≤(Φ b)⁻¹ → k₁ ≤ R.alloy.B.a.clock.J b → Extra.Multi.Occupancy (o b) k₁ → (
          ∀ (l:Type)[Countable l] (D': Lamps (Affinity.Wallet Actors) l G (Ψ b).p (o b) J), Affinity.Taut (Loc b) Actors uK D' → RootsE D' w ((Ψ b).p.supportExponent+2) e → Origin.Global D' w ((Ψ b).p.supportExponent+2) e → ∃ K:QuadraticLocal.Hard (Affinity.Wallet Actors) (Ψ b).p (Ψ b).activities.forced (Ψ b).activities.K (o b) J,(∃ T', ( Votes (N:=N) R D Q Ψ Q0 Uq D0 Actors uK o Loc w q b m k₁ e (embark R Ψ Actors o D' K) T') ) ∧ Throng.Hard.Pair K w (Ψ b).p.B (Ψ b).p.supportExponent (forcedDivisor Z b*(Φ b)^(-(q:ℝ))) ((forcedDivisor Z b*(Φ b)^(-(q:ℝ)))*e) ∧ ∀ a U, Summable (fun j=>QuadraticLocal.Neighborhood.Origin.whole D' a j U) ∧ ((embark R Ψ Actors o D' K).canvas).density a U= (↑((Ψ b).eval U):ℂ) • ( Poly.pass (∑' j, QuadraticLocal.Neighborhood.Origin.whole D' a j U) ) )
          ∧ (∀ (V':Estate ( Affinity.Wallet Actors ) (o b) (Ψ b) J), Affinity.Collared (Loc b) Actors uK (Ψ b) V'.canvas →RootsE V'.canvas.E w ((Ψ b).p.supportExponent+2) e →RootsK V'.canvas.K w ((Ψ b).p.supportExponent+1) e → ∃ T', Votes (N:=N) R D Q Ψ Q0 Uq D0 Actors uK o Loc w q b m k₁ e V' T')
include C g Yq D0 hw' HP
set_option maxHeartbeats 680000
lemma arena (x₀ mH d₀ qx qV M1:ℕ) (ε:ℝ) (hV:0<ε) (hE: ε ≤ 1/8) (hspan:0≤ℓspan)(hd:0<δ) : ∀ᶠ b:ℕ in atTop, ∀ m≤ b,PaceR.Close R mH ℓspan m b→ Boot.Alumni R D Q Q0 Z' Qa x₀ mH d₀ ε ℓspan b m ∧ Licence (k:=k) R D Q Q0 Uq D0 qx qV M1 m b δ := by
    filter_upwards [Boot.lectures R g D Q C Q0 Z' Qa Yq hw' x₀ mH d₀ ε ℓspan hV hE hspan, Orbit.cap R g D Q Q0 Uq D0 δ mH M1 ℓspan hspan hd,(on_tail R g mH ℓspan (max qV (qx+1)))] with b he h hm m hp hC
    obtain ⟨hv,ht⟩:= sup_le_iff.mp (hm m hp hC); refine ⟨he m, ⟨fun i hi hb=>⟨(h i m hi hb hC).2,(h i m hi hb hC).1⟩,⟨ht,hv.trans ((S).fits.mono hp)⟩,?_⟩⟩
    intro N n hN π Γ Ψ v hP θ _ _ J X' a1 a2 Actors _ uK o Loc hO hL w hw e k₁ h1 h2 hz hΩ
    constructor
    · intro l _ D' hy hV hA; exact Orbit.minted R g D Q π Γ Ψ v C Q0 Uq Yq.employed D0 HP Actors uK o Loc w hw hO hL e hΩ h2 hN D' hP h1 hp hz ht hy hV hA
    intro V h H₀ B; exact Orbit.promotes R g D Q π Γ Ψ v C Q0 Uq Yq.employed D0 HP Actors uK o Loc w hw hO hL e hΩ V h1.le h2 hN hp hz ht h H₀ B
end Orbit
end Moonlight
end Sycamore
end YM.QuadraticLocal.Advent
