import YM.AllOrder.Transit.Monarchy
import YM.QuadraticLocal.Vacuum.Purchase
/-!
# Existing folding mechanism, with a general old-E budget.

 Adapted from Transit.Monarchy -- factor retained through BOTH support gates.
-/
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
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm
open Burn Carillon Cap
open Rosary.Repair
open Transit Transit.Moon Transit.Moon.Kit
open Floe Floe.StateE
open Step PlanV Roost
variable {G:Gauge}{X:Metals G}{D:Rolls X.p} (R: Roots (G:=G) X.p.profile X.K X.p.kernel) (Q:R.Tab D)(A:Alloy X D)(F:Factor A)
namespace WheelP
variable {m n k N:ℕ} (h:Pass R Q A F)
local notation "S"=> X.p
set_option quotPrecheck false
local notation "a"=> A.B.a
local notation "C"=> X.p.profile
local notation "E"=>A.B.a.clock.J m
local notation "Y"=> A.B.a.clock.J (m+1)
local notation "V"=> A.B.a.budget m
local notation "y"=> A.B.a.clock.hatBeta m
local notation "L"=> D.L Y
local notation "t"=> betaF G y L
local notation "s"=> (C E)
local notation "W"=> A.B.a.budget (m+1)
local notation "B"=> radiusB y
local notation "g"=> A.B.a.S.block m
local notation "T"=> F.target Y E
local notation "P!"=> (F.expense Y E)
local notation "p"=> A.B.a.params m
local notation "z"=> Burn.horizon k
variable (g0:G.Simple)(hm:m<N)(hk:Burn.horizon k+2≤ A.B.a.clock.J m)
local notation "G0"=> Shop.parking (Shop.tall E) ((T).halo)
local notation "Δ0"=> 1+cloak D (Y)
local notation "δ"=> (A.B.a.params m|>.width)
variable (X': Card D R (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (A.B.a.clock.adm (m+1)) (Burn.horizon k))(hh:Journey R A (m:=m) (N:=N) X') -- syntax
local notation "Ω"=> litP R A Q hk X'
local notation "Plead"=> lead R Q A hk X'
local notation "W'"=> (C Y)
local notation "fφ"=>R.pre z Y
variable {c f: Side} (u:f.val=c.val*(A.B.a.S.block m).val)(x:ℝ)(hx:x∈band A.B.a (m+1))
set_option quotPrecheck false
local notation "D'"=> Pane.orchestra A N (m:=m) u
local notation "Ξ"=> goldN R Q A hk X' x
local notation "ℳ"=> M0 k 0 W X'.extra x
local notation "MNew"=> M0 k 0 V Plead (Ξ)
local notation "φ"=> youth (N:=N) R A X' u x
local notation "E'"=> A.B.kin.alpha N m
local notation "Sℓ"=> Pane.panel A m u
variable {U:RG.Rep G f} (K:Chartlet F.shape A N m u U)(hz:SeekR F.shape A N m u K) (hs : U.beta=x)
local notation "Op"=> Chi.canonical
local notation "Γ"=> (Ξ-x)
local notation "M★"=> organ (K) Op Ξ Γ
local notation "D0"=> (posting V K)
local notation "k₀"=> (Ω)
local notation "R₁"=> A.B.kin.path N m
local notation "P'"=> (F.expense Y E)
local notation "G'"=> lump G L y s
local notation "V'"=> Cash.armK (T) L (F.shape.μ Y E) y 0 (P').degrees
local notation "n'"=> (s).order
local notation "E₀"=> F.expense Y E
local notation "τ"=> alt k
local notation "v₀"=> pen G L k y 0
/- two arrivals facts integrated. percent.N lyric burn.Eval. -/
variable (hB:U.p=A.B.a.budget (m+1)) (C₀: Burn.Seed U (M0 k 0 (A.B.a.budget (m+1)) (X'.extra) x))
local notation "v!"=> V -- notation V already cheap
local notation "M"=> Set.range C₀.model
variable {C' D'ξ v T' u' b r B' q i : ℝ}{l:ℕ} -- B exists
variable (K': Captain K ((X.p.profile (A.B.a.clock.J m)).order) C' D'ξ v T' u' b r B' q l Chi.canonical)
local notation "T0"=> tiredT K (typeT M k) (alt k)
local notation "S0"=> (fun i=> Song.sequence K (Match.staple (H:=K) («J»:=K) rfl rfl rfl) Op i)
local notation "ϕ"=> poem R A F X' u x K C₀
include h hk hm hB hx hz hs hh
lemma shiningW {b' z':ℝ} (hb : Ac.Hit (Captain.reachability (H:=K)) (radiusB y) (fun χz=>if tiredT K (typeT (Set.range C₀.model) k) (Burn.alt k) χz then ConnectedActivityE6.Blaze.March.Captain.markΦ K' χz ((C E).power) else 0) ((P').earn) z') (hh' : haze (k:=k) (Mξ:=Set.range C₀.model) A F u K b') : ∀ᶠ u':ℕ in atTop, Meadow.Budget V (Beam.marquee K V).reg (linger (ϕ u') Op u' Ξ Γ).logRead (away s*((z'+b')+v₀)+v₀):=by
 let hS:= guidance R Q A F h hm hk X' hh u x hx K hz hs (Classical.choice (Tree.select (Sℓ).ratio (Sℓ).patch.odd_side)); obtain ⟨ht,hV,hQ⟩:=song_price R Q A F h hm hk X' hh u x hx K hz hs; have hTy:= low_tent R Q A F h hm u K
 obtain ⟨hv,ho,hx'⟩:= (zones R Q A F (m:=m) h).2.1; have hr : Meadow.Budget V (Beam.dashboard K) (fun i=> if T0 i then S0 i else 0) z':= High.hit_trust _ _ _ K' hb rfl rfl ho.le hv.le (by unfold preExponent; rw [hx']; exact F.pledging.agenda _ _ (step_paid (a) m)|>.1); let P:= V; let Δ:=burnoff K M k; have hy : Meadow.Budget P (Beam.dashboard K) (fun i=> @ite _ (Δ i) (Classical.propDecidable (Δ i)) (S0 i) 0) (z'+b'):=by
    let f := fun i=> if (T0) i then S0 i else 0; let g' := fun i=> if ¬T0 i ∧ errorX K M i then S0 i else 0; have heq:f+g'=(fun i=> @ite _ (Δ i) (Classical.propDecidable (Δ i)) (S0 i) 0):= funext (fun i=>by by_cases he:T0 i <;> by_cases hx : errorX K M i <;>simp [Δ,burnoff,he,hx,f,g']); exact heq ▸ High.chan_budget _ _ f g' hr hh' -- explicit
 let hu':= (V).threshold; let hX := (bless R Q A F h hk).1; have hC : preExponent (V)/(V).B ≤(δ)/4:= (div_le_div_of_nonneg_right (show preExponent V≤preExponent V +1 from le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg _)).trans hX.2.2;
 rw [← ht]; refine Carillon.finite_bonusC («α»:=Δ) _ _ Ξ Γ hS (ϕ) (fun i he hp=> ?_) (cruiseC _ _ _ Ξ Γ hy rfl hTy.1 hTy.2.2.2.2 hC hQ) (Real.rpow_pos_of_pos (by have hv:=zones R Q A F (m:=m) h |>.2.2.2.2.2.2.2; exact zero_lt_one.trans hv) _); -- first _. ∀T
 obtain ⟨u,hU⟩:=hp; exact Burn.pursuit Op k (by rw [hB]; exact (zones R Q A F (m:=m) h).2.2.2.2.2.2.1) i he u hU

end WheelP
end YM.AllOrder.Transit
