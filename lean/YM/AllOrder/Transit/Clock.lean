import YM.AllOrder.Transit.Economy
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Transit
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
namespace Moon
variable {G:Gauge}
open Burn Carillon Carillon.Cap Floe
open Step PlanV
open Wheel Wheel.Ride
-- Workspace projection permits chosen Eta. articulate support bounds for Holder.Point.V.Window projections & loss.SX.
local notation "Z"=> Set.Icc
namespace Kit
variable {X:Metals G} (R:Roots (G:=G) X.p.profile X.K X.p.kernel)(D:Rolls X.p)(Q:R.Tab D) {i j:ℕ} (h:StepStages j i) (hF:4≤j){W:ℝ}{P:Teller G} (U:ConnectedActivityE6.Target G P)(o:Target.Order G W) (μ:ℝ) (hμ:0<μ) (he:U.table=X.O)
local notation "E"=> (X.p.profile i)
local notation "L"=> D.L j
local notation "Y"=> Shop.parking (Shop.tall i) U.halo
local notation "q"=> Testing.query X.p X.K j i
local notation "τ"=> Trio.paySide G L Y
variable (k:ℕ) (hk:Burn.horizon k+2≤ i) (hp:Nonempty (Card D R j i hF (Burn.horizon k)))
local notation "u"=> Burn.horizon k
local notation "A"=> Q.income j i hF h u hk hp
local notation "w"=> (fun t=> ((τ t):ℝ))
local notation "ε"=> - (3/8:ℝ)*(Burn.alt k:ℕ) -- negative lower bound? need cast.S.Profit
abbrev hike (k:ℕ):ℝ:= (credit k-1/80+1/400)
structure Pure (G:Gauge) (y:Stage) (Lξ:Side)(v:ℕ)(η t:ℝ) : Prop where
    room : let c:=Trio.base v (radiusB t); ∀ P:BudgetPoint,P.threshold≤2*Pressure.fiery G t Lξ → ∀ m n:Side,2*c< m.val→ ∀ r:ℕ,r+1≤c→ ∀ (h:2*r≤ n.val)(f:Site m)(U':Config G m),Healthy P.threshold (neighbors c f) U'→ ∃ (z: Site n→ G.El)(s: Positions (Uniform.Primary n G)), actual s=Lattice.gauge z (Slide.shape (Slide.cognac h) f U')∧ ‖s‖+2*furl G Lξ t < Pair.velocity G Lξ η t
    budget : ∀ (P:BudgetPoint), P.threshold=temp t→ P.threshold ≤2*Pressure.fiery G t Lξ→ P.order=y.order→∀ (c:Side) (V:Positions (Uniform.Primary c G)),‖V‖+2*furl G Lξ t < Pair.velocity G Lξ η t → flags P.threshold (actual V)=∅ → ∀ (S:ℕ→ RegularAddress c) (l:ℕ→ Config G c →ℝ)(U' f:Config G c→ℝ)(s b z:ℝ), Meadow.Budget P S l b → P.Regular univ U'→ (∀ V∈ sunny P,f V=z-U' V-Boulevard.throng l V) →(∀ V':Positions (Uniform.Primary c G),‖V'‖+2*furl G Lξ t< Pair.velocity G Lξ η t→ actual V'∈sunny P→Brush y.order s (Pair.velocity G Lξ η t)⁻¹ ((stillA f)∘ actual) V') → ∀ l:List (Directions G c),l.length≤P.order→(∀ i∈l, ‖i‖≤P.threshold)→ ‖leftDerivs (stillA U') l (actual V)‖ ≤ Boulevard.ticket y.order s+2*((Fintype.card (Site c):ℝ)*b)
lemma pure_post (G:Gauge)(S:Stage)(Lξ:Side)(x:ℕ) : ∀ᶠ e in 𝓝[>] (0:ℝ),∀ᶠ t:ℝ in atTop,Pure G S Lξ x e t:= by
 filter_upwards [YM.PertExtension.Series.Tested.eventually_small (show 0<(1/8:ℝ) by norm_num)] with i hi; let b:= Pair.tunnel i; have hv:-(1/2:ℝ)<b:= lt_add_of_pos_right _ hi.1; have hw:= hi.2; filter_upwards [Trio.pledges_slender hv G Lξ (fun v=>Trio.base x (radiusB v)) (Trio.rows G Lξ x|>.2.2.1.uses), Boulevard.rising_slender G Lξ hv (by unfold b Pair.tunnel; linarith) S.order] with i ht hw; exact ⟨ht,hw⟩
-- choose K once before Years. Also offset.Dues uses actual b.β etc. Glow Prop include countability.Asympt.
def Figure (t:ℝ):= ∃ j' :ℕ, (X.p.profile i).order ≤ j' ∧ ∃ η:ℝ,Pair.Glow D R j i hF («w»:=w) (A) μ W U o j' (hike k) t η ∧ Pure G E L Y η t ∧
 ∀ a:Card D R j i hF (Burn.horizon k), a.self.paid=strengthP (betaF G t L) → ∀ β, β∈Set.Icc (betaF G t L/2) (2*betaF G t L)→ |Pair.δE D R j i hF A a β| ≤ 1 ∧ Burn.Near t (now ((A).issue a) (Burn.horizon k+2) β)
include hμ he
lemma house (g:G.Simple) : ∀ᶠ t:ℝ in atTop, Figure R D Q h hF U o μ k hk hp t:= by
 let n':=(E).order + Burn.horizon k+5; let z:= hike k; obtain ⟨q',r,hr,hR⟩:= Aux.Name.sale G L (u+2) n' (Catch.graded (u+3)); obtain ⟨W'⟩:= Push.Uniform.pre_order G (X.p.profile j).width (X.p.profile j).paths (Mural.sheet X.p D hF).J X.p.kernel (n:=r+3+3) (by omega);
 have hz : Catch.graded (u+3)<z:= by unfold z hike Catch.graded; rw [sale_eq]; push_cast; linarith
 have ha := Pair.lucid D R j i hF W' A μ W U o he g (Trio.circles G (D.L j) (Y)) hR hr (by omega) z hz hμ -- arg order!
 obtain ⟨e,h₁,h₂⟩:= (ha.and (pure_post G E L Y)).exists; filter_upwards [h₁,h₂,Pair.prior_d D R j i hF A, Pair.fee_delta D R j i hF A 0 (by norm_num)] with t hT he ht hp; refine ⟨n',by unfold n'; omega,e,hT,he,fun a he β hβ=> ⟨ (hp a he _ hβ).trans (by rw [Real.rpow_zero]), ht a he _ hβ ⟩⟩
end Kit
end Moon
end YM.AllOrder.Transit
