import YM.AllOrder.Horizon.Connect

/-!
# Checkpoint consumer (leading-order AND high-order local estimates)

Run on SAME real layout V→W for all fields. Not iterate error budget. PURE
vacuum-only path `Y`, not full Q. Includes high-cost cut in all true weights,
exact FULL-density reclosure and Markov post kernel, stencil transfer implication
for the remaining (canonical packet) calculation. Supplies concrete diagnostic
`k` desktop analysis of true physical step, not only Desk hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Shop
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High Roost Graces Extra.Histories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} {D: Rolls X.p} (A : Alloy X D) (F: Factor A) (B : Org.Bolt A) {c f : Side} {m n N : ℕ}
local notation "a" => A.B.a
local notation "J" => (A.B.a.clock.J (m+1))
local notation "I" => (A.B.a.clock.J m)
local notation "L" => (D.L J)
local notation "x₀" => (A.B.a.clock.hatBeta m)
local notation "z" => betaF G x₀ L
local notation "V" => A.B.a.budget m
local notation "P" => (F.target J I)
local notation "R" => F.shape
local notation "Ω" => (F.expense J I)
set_option quotPrecheck false
local notation "E" => X.p.profile I
local notation "u" => (tall I)
local notation "Y" => (parking u (P).halo)
local notation "d" => (Meadow.studio Y (radiusB x₀))
local notation "e'" => Trio.base Y (radiusB x₀)
local notation "g'" => B.history N n (m+1)
local notation "Π" => (A.B.a.S.oneStep m n).exact_size
local notation "S" => (Pane.orchestra A N Π)
local notation "βp" => (g').beta
local notation "Y'" => (Pane.virgin (Pane.orchestra A N Π) (A.B.a.budget (m+1)) βp)
local notation "P0" => (A.B.a.budget (m+1))
include F B
variable (m n N)
lemma buys_pure (H:Shop.Pledged A F) (hm : m<N):
   ∃ (Q: Chartlet F.shape A N m Π (Pane.virgin (Pane.orchestra A N Π) (A.B.a.budget (m+1)) ((B.history N n (m+1)).beta))) (h:LineCare N m A F βp), SeekR F.shape A N m Π Q ∧
   (∀ᶠ k:ℕ in atTop, HasLedger A F Π Q h k) ∧ ∀ (i:Stars) (K:Forest (Pane.panel A m (side_pure A F (m:=m) i)).ratio),
   let V₀:= Pane.orchestra A N (side_pure A F (m:=m) i); let C:=size_pure A F (m:=m) i
   ∃ (ρ:Bid.Dir G (size_pure A F (m:=m) i)→ AxisChart G K),
   Critical («S»:=Pane.panel A m (side_pure A F i)) K V₀.high V₀.up ρ ∧
   ClassicalMatch K V₀.high V₀.low V₀.up V₀.down ρ ∧
   ∀ (k:ℕ) (x:Positions (Uniform.Primary (size_pure A F (m:=m) i) G)), k ≤ I → flags (Pressure.temp x₀) (actual x)=∅ → ‖x‖+2*furl G L x₀<eaves G L x₀→∀ (l:(Pane.panel A m (side_pure A F i)).Choices) (r:ℝ), ‖(gStep βp,x)‖ ≤ r → r < eaves G L x₀ →
    0<Token.tramp V₀ P0 βp x∧ Brush ((E).order+I+3) (z^edgeW I*(z*r^(k+3)+r^(k+1))+ z^(seam_hat I)) r⁻¹ (Token.pures V₀ P0 βp- Local.Pure.script K V₀ X.O ρ βp l k) x := by
  have he:(g').beta∈band A.B.a (m+1):= ((B.sticks N n).prices (m+1) (Nat.zero_le _) hm).2
  have hp := room_full A F (m:=m) (n:=n) H.1; obtain ⟨h⟩:= buyings A F hm he
  obtain ⟨Q,hQ⟩:= Pane.affords A N Π hm (show 100*(1+radiusB x₀) ≤ (A.B.a.S.side m n).val from (by unfold Trio.base Trio.tent at hp; omega)) F.shape F.pledging.conducts.income.grow.1 F.pledging.conducts.full he
  refine ⟨Q,h,hQ, Shop.fit A F H.1 Π Q hQ hm H.2.2.1 rfl rfl he hp h H.2.1 (fun i=>rfl), fun i K=> ?_⟩
  exact Shop.desk A F H.1 (side_pure A F i) (h.bought i) hm rfl (Trio.taller ..)

end YM.AllOrder.Shop
