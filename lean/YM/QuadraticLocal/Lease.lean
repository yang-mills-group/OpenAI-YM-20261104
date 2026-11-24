import YM.AllOrder.Transit.Merit
import YM.AllOrder.Transit.Invite
import YM.QuadraticLocal.Kiosk
/-!
# First qlocal packing receipt for future marks transport

Extensions of the proof in `AllOrder/Transit/{Stead,Invite}`. Track full K pricing; transfer
not split into quiet and evaluated. New support predicates stay inside repeated footprints.
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
-- Lore.C all leg paths on Star(s).Housing.Can Request Geometry.Progress. Bake budgets regular. core.
local notation "d'"=>Meadow.studio G0 B
local notation "D★"=>Trio.base G0 B
local notation "τℓ"=> Trio.tent G0 B
local notation "Δ"=> ends_ A F (m:=m)
local notation "ϕ"=>patchF A F (m:=m)
variable (J: Suite R A F X' x N)
local notation "ℓ"=> Shop.clock_pure A F (m:=m)
local notation "w"=> (render R Q A F hk X' x J)
variable (c₁: Burn.Seed U (M0 k 0 (A.B.a.budget (m+1)) (X'.extra) x))
local notation "Z'"=> poem R A F X' u x K c₁
variable (j:ℕ)
local notation "U★"=> (stash (Z' j) Op V Ξ Γ MNew ℓ (D★) (w j) j)
variable (hu:U.p=A.B.a.budget (m+1))(he:U.path=A.B.kin.path N (m+1))
    (hG:2*Trio.base (Shop.parking (Shop.tall (A.B.a.clock.J m)) ((F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo)) (radiusB (A.B.a.clock.hatBeta m)) < c.val)
local notation "PP"=> (line R Q A F hk X' u x K J c₁ j)
open Marlin Progress.DirectedRecipe Time
local notation "U₀"=> agora K V D★
local notation "T0"=> pluck V (U₀)
local notation "D₀"=> poursP V (U₀) U★
local notation "St"=> PostP.θ1 G s y k
local notation "v'"=> Cap.authentic G L y s k
local notation "W0"=> Time.forecastK (a) m F.scout x
section
include h he hu hm hk hx hh g0 K hz hs hG
local notation "s0!"=> Marlin.pluck
-- use looser/harder revenue v/8 (exact reserved from billing steps).
include J c₁ in
lemma rolls_paid (i:ℕ) : let Y₁:=(Beam.marquee K V); let W₁:=linger (Z' i) Op i Ξ Γ; Nonempty (QuadraticLocal.Kiosk.First V (Refrain.read K (Match.staple (H:=K) («J»:=K) rfl rfl rfl) Op Y₁.reg W₁.logRead) ((Marlin.pluck V U₀).read (Marlin.poursP V U₀ (stash (Z' i) Op V Ξ Γ MNew ℓ (D★) (w i) i))) (W0 /8) W0 ((V).supportExponent+1)) := by
    intro Y₁ W₁
    let t':= Cap.stem G L y s G0; let U':=Marlin.tithe (2*D★) t' V (coverTicket G0); have hY:= safe R Q A F h g0 hm hk X' hh u x hx K hz hs J c₁ i hu he hG; have hT:0≤t':= (norm_nonneg _).trans (hY 0|>.2.2 1); have hh':0≤ U':= by unfold U' Marlin.tithe; positivity
    let v₁ β := (F.scout Y E).pair.strong t β; let Θ:= Match.staple (H:=K) («J»:=K) rfl rfl rfl
    have hv : inBand t x:= by rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in hx
    have heq : W0=v₁ x:= by unfold Time.forecastK; rw [PriceCompiler.beta_eq A.B.valid]
    have hV:0≤ v₁ x:= mul_nonneg (F.scout Y E).pair.C_nonneg (Real.exp_nonneg _)
    have hp: U'≤t^( -(1/8:ℝ)):= (bless R Q A F h hk).2.2.1.curtain
    obtain ⟨b,hR⟩:= (F.inn.terms.allot _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)|>.2.2.1) x hv (v₁ x/8) U' (div_nonneg hV (by norm_num)) hh' le_rfl hp; rw [heq]
    -- hard reserve at 1/8 with "+2" after.Force orientation untouched.
    let K₀:= ornament (c:=c) ℓ (w i); let P₀:=line R Q A F hk X' u x K J c₁ i
    exact QuadraticLocal.Kiosk.launch Y₁ D★ (2*D★) W₁ K₀ P₀ (fun i=>(hY i).1) (fun i=>(hY i).2.1) (fun i=>(hY i).2.2) (fun i=> by unfold coverTicket; apply Nat.cast_le.mpr; apply le_trans (Trio.scaleMeters G0 B (V).B_pos i _ le_rfl); rw [two_mul]) hR
include J
lemma first_class (hA: ∀ᶠ z' in atTop, propume R Q A F hk X' u x K c₁ z') : ∃ (D'':Listing G c)(Zℓ:Collection.Source G c)(ℓ₀:ℝ), Collection.Local D'' (V) Zℓ St W0 ∧ ((Sℓ).push x U.eval= fun V₀=>sublet R₁ D'' Zℓ MNew (s) V x Γ ℓ₀ V₀) ∧ ∃ E₁ X₀, Nonempty (QuadraticLocal.Kiosk.First V (Refrain.read K (Match.staple (H:=K) («J»:=K) rfl rfl rfl) Op E₁ X₀) (D''.read Zℓ) (W0/8) W0 ((V).supportExponent+1)) := by
 let s':= Classical.choice (Tree.select (Sℓ).ratio (Sℓ).patch.odd_side); let Vmark:= J -- J Suite not included
 obtain ⟨j,hj⟩:= (hA.and (petals R Q A F h g0 hm hk X' hh u x hx K hz hs J hG)).exists; obtain ⟨b,hε⟩:= hj; let U' := stash (Z' j) Op V Ξ Γ MNew ℓ D★ (w j) j; let H:=poursP (V) U₀ U'; let v:= Song.weighty K Op s'; let f:= Carillon.Lum (Z' j) Op Ξ Γ MNew j 0 (1:Config G c); have hΓ:= computes R Q A F h g0 hm hk X' hh u x hx K hz hs J c₁ j hu he hG
 refine ⟨ T0, H,v-f, ?_, funext fun v₁=> ?_,_,_, rolls_paid R Q A F h g0 hm hk X' hh u x hx K hz hs J c₁ hu he hG j⟩
 · have hh:Collection.Local (T0) V H (v'+turnFee V*Cap.footprint G L y s k G0 V) W0:= Carillon.mentor (Z' j) Op V Ξ Γ MNew ℓ D★ (w j) (k:=j) hΓ b hε; obtain ⟨z',hv,hX⟩:=hh.cheap; exact {hh with cheap:=⟨z',hv,fun i=>budget_loosen (hX i) ((bless R Q A F h hk).2.2.1.middle)⟩}
 obtain ⟨Dξ,d,vh,p₀,b',t',s₁,s₂,w₀,i,n₁,K₀,hK⟩:= Shop.appointed A F h.formal.ladder u hm K; have he: (V).order ≤(s).order:= (zones R Q A F h).2.1.2.1.le; have h1:= applies R Q A F h hm hk X' hh u x hx K hz hs s' he K₀ v₁;
 have hm' := (K.laws.data.room.buys); have hB:= paint R Q A F h g0 hm hk X' hh x hx (show 4 ≤ c.val from (by omega)); let p':= V; have hb' := Carillon.value (k:=j) (Z' j) Op V Ξ Γ MNew ℓ D★ (w j) (guidance R Q A F h hm hk X' hh u x hx K hz hs s') hB.2.1 hB.1 hΓ b v₁ x (Song.weighty K Op s') 0; change (Sℓ).push x U.eval v₁ = _; rw [hs] at h1; rw [h1]; refine hb'.trans ?_ ; have he:(s).clip=(p).clip:= congr_arg RG.Stage.clip (params_eq A.B.valid m).symm; rw [sublet, Rosary.Guard.portal,hallelujah, earlyValue, he]; -- track associativity.Same.
 change (_*Real.exp _ * Real.exp _)* Real.exp _=_; rw [mul_assoc, mul_assoc,← Real.exp_add,← Real.exp_add]; -- may wrong he mapping
 congr 2; rw [show (Pane.orchestra A N u).down=(A.B.kin.path N m) from rfl, show (Pane.orchestra A N u).low=(A.B.a.params m).clip from rfl]; ring
end
end WheelP
end YM.AllOrder.Transit
