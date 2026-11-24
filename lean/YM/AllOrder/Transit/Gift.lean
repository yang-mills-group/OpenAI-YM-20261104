import YM.AllOrder.Transit.Cross
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
-- Lore.C all leg paths on Star(s).Housing.Can Request Geometry.Progress. Bake budgets regular. core.
local notation "d'"=>Meadow.studio G0 B
local notation "D★"=>Trio.base G0 B
local notation "τℓ"=> Trio.tent G0 B
abbrev ends_ := Trio.fence G0 B
local notation "Δ"=> ends_ A F (m:=m)
abbrev patchF (i:Stars):= Shop.side_pure A F (m:=m) i
local notation "ϕ"=>patchF A F (m:=m)
structure Suite (N:ℕ) where
 view (i:Stars) : Chartlet F.shape A N m (Shop.side_pure A F (m:=m) i) (youth (N:=N) R A X' (Shop.side_pure A F (m:=m) i) x)
 seek i: SeekR F.shape A N m _ (view i)
include h hm hk g0 hx hh
local notation "C₀"=> Suite R A F X' x N
lemma quoteF : Nonempty C₀:= by choose h hh using fun i:Stars=> tokens R Q A F h g0 hm hk X' hh (ϕ i) x hx (Trio.highChair ..|>.2); exact ⟨h,hh⟩
variable (J: Suite R A F X' x N)
abbrev render (j:ℕ)(i:Stars):= brook R Q A F hk X' (ϕ i) x (J.view i) (youthS R A X' _ x) j
local notation "ℓ"=> Shop.clock_pure A F (m:=m)
local notation "w"=> (render R Q A F hk X' x J)
abbrev ζhat := Cap.micro G L y s G0
local notation "T!"=> ζhat A F (m:=m)
variable (c₁: Burn.Seed U (M0 k 0 (A.B.a.budget (m+1)) (X'.extra) x))
local notation "Z'"=> poem R A F X' u x K c₁
variable (j:ℕ)
abbrev line (j:ℕ)(i:Site c):= Carillon.loss (poem R A F X' u x K c₁ j) Op V Ξ Γ MNew ℓ D★ (w j) j i
local notation "U★"=> (stash (Z' j) Op V Ξ Γ MNew ℓ (D★) (w j) j)
include K hs c₁ hz
open Till WilsonStartup
lemma heat (o:Site c) (U:Config G c)(hu: flags (V).threshold U=∅) : ‖brook R Q A F hk X' u x K c₁ j o U‖≤ T!:= by
 let v := guidance R Q A F h hm hk X' hh u x hx K hz hs (Classical.choice (Tree.select (Sℓ).ratio (Sℓ).patch.odd_side)); have he:=chamber_valueC («k»:=j) (Z' j) Op V Ξ Γ U rfl (scenery R Q A F h hk X' u x K c₁ j) (Shop.perimeter ..) o v hu; refine (norm_sub_le ..).trans (add_le_add he ?_); exact (show ‖MNew c o U‖≤ Cap.fee1 G L y from (((paint R Q A F h g0 hm hk X' hh x hx (show 4≤c.val from by have h:=K.laws.data.room.buys;omega)|>.1) o).cap.2 U (by simp [Healthy,hu]) [] (by simp) (by simp)).trans ((bless R Q A F h hk).2.2.2.1 _ ((mates R Q A F h hm hk X' hh x hx).2.1)))
omit K hs c₁ hz in
lemma panoramic (i:Stars)(x':Site (Δ i)): (V).Regular univ (w j i x'):= CouplingShape.reg_extend (streamlet R Q A F h g0 hm hk X' hh (ϕ i) x hx (J.view i) (J.seek i) rfl j (youthS R A X' _ x) _) (subset_univ _)
variable (hu:U.p=A.B.a.budget (m+1))(he:U.path=A.B.kin.path N (m+1))
    (hG:2*Trio.base (Shop.parking (Shop.tall (A.B.a.clock.J m)) ((F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo)) (radiusB (A.B.a.clock.hatBeta m)) < c.val)
include hu he hG
local notation "PP"=> (line R Q A F hk X' u x K J c₁ j)
lemma safe (i:Site c): Tidy V (neighbors (2*D★) i) (PP i)∧ (∀ U,PP i U≠0→ ¬Healthy (V).threshold (neighbors (2*D★) i) U)∧ ∀ U,‖PP i U‖≤ Cap.stem G L y s G0:= by
 let H := guidance R Q A F h hm hk X' hh u x hx K hz hs (Classical.choice (Tree.select (Sℓ).ratio (Sℓ).patch.odd_side)); let S':= Z' j; let H':Stars→Side:=Δ; have ht := paint R Q A F h g0 hm hk X' hh x hx (show 4≤c.val from by have h:=K.laws.data.room.buys;omega); have hp:=ht.1
 have hY : ∀ i∈S',∀ x∈perf K i,perf K i⊆ neighbors (d') x:= scenery R Q A F h hk X' u x K c₁ j; have hw:B+B≤ d':=Shop.perimeter ..; have hm' : Trio.tent G0 B+4 ≤ D★:=by unfold Trio.base;omega
 refine ⟨Carillon.percolate (k:=j) S' Op V Ξ Γ MNew ℓ D★ (w j) H hp rfl hY hw i (panoramic R Q A F h g0 hm hk X' hh x hx J j) hm' (by unfold Trio.base Trio.tent;omega) le_rfl,fun U hV hx=>hV ?_,fun U=> ?_⟩
 · have hg(p₀:Stars): 4*d'+16 ≤ (Δ p₀).val:= Trio.highChair ..|>.1; have hc :4*d'+16≤ c.val:=by unfold Trio.base Trio.tent at hG;omega;
   let g':=fun j=> w j; have hK:CompatibleP V (d') (Lum (Z' j) Op Ξ Γ MNew j) (w j):= ⟨fun p₀=> Carillon.entwines _ _ _ _ _ (Tilt.signed _ _ _ _ _),fun i j'=> beehive R Q A F h g0 hm hk X' hh (ϕ i) x ‹x ∈ Shoot.band A.B.a (m+1)› (J.view i) (J.seek i) rfl j (youthS R A X' _ x) rfl rfl (ϕ j') (hg i) (J.view j') (J.seek j') rfl rfl rfl _ (hg j'),fun k=> beehive R Q A F h g0 hm hk X' hh (ϕ k) x ‹x∈Shoot.band _ _› (J.view k) (J.seek k) rfl j _ rfl rfl u (hg k) K hz hs hu he c₁ hc, fun i => (streamlet R Q A F h g0 hm hk X' hh u x ‹x∈Shoot.band _ _› K hz hs j c₁ i).sites ⟩
   exact Carillon.cool S' Op V Ξ Γ MNew ℓ D★ (w j) U H hp rfl hY hw i le_rfl (by unfold Trio.base Trio.tent;omega) hm' (by unfold Trio.tent;omega) hc (by unfold Meadow.studio Meadow.roomSize; omega) hK hx
 let y₁:=Cap.fee1 G L y; have hv:0≤ y₁:=(by have hz:=zones R Q A F (m:=m) h |>.2.2.2.2.2.2.2; apply Real.rpow_nonneg (zero_le_one.trans hz.le))
 have hv' : PostP.C' V G k Ξ y≤ y₁:= (bless R Q A F h hk).2.2.2.1 Ξ ((mates R Q A F h hm hk X' hh x hx).2.1); let P:= V; have hp' x:= Fairness.le (hp x) hv'; refine le_trans (safety S' Op V Ξ Γ MNew ℓ D★ (w j) U H hp' rfl hY hw i (fun _=> T!) ?_ hm') ?_
 · intro i q hu y'; exact heat R Q A F h g0 hm hk X' hh (ϕ i) x hx (J.view i) (J.seek i) rfl (youthS R A X' _ x) j y' q hu -- args order
 unfold Cap.stem; apply add_le_add _ le_rfl; exact add_le_add le_rfl (le_add_of_nonneg_right hv)
end WheelP
end YM.AllOrder.Transit
