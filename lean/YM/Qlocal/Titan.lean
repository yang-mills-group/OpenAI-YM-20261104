import YM.AllOrder.Transit.Invite
import YM.Qlocal.Flight

/-! Strengthens WheelP.invested: includes analytic purchases for the strong
  marked reserve as the real SOFT loss (lattice boundary etc) is charged to
  the K ledger. Output contains the strong POCKET every query on every test
  space buys the data trace. Same representation, NO separate stubs activated
  as positive replacement.Budget after +1+1 entry buys unmarked healing with
  unchanged marker fugacity on all Degrees switched at once. Does NOT yet
  attempt to add more marked realignment labels (with their own spill costs).
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
open Qlocal
local notation "X0"=>((Beam.marquee K V).read (Song.plusone K (Match.staple (H:=K) («J»:=K) rfl rfl rfl) Op E'))
local notation "One"=> (V).supportExponent+1
local notation "Costs"=> KLink V X0 (W0/8) (One+1) V
include h g0 hm hk hh hx hz hs J c₁ hu he hG
lemma healing : Nonempty (KLink V X0 (W0/8) (One+1) V ((T0).read D₀) W0 ((V).supportExponent+1)):= by
  let t':= Cap.stem G L y s G0; let H:=U₀; let Z:= U★; let U₁':=Marlin.tithe (2*D★) t' V (coverTicket G0); have hY:= safe R Q A F h g0 hm hk X' hh u x hx K hz hs J c₁ j hu he hG; have hT:0≤t':= (norm_nonneg _).trans (hY 0|>.2.2 1); have hh':0≤ U₁':= by unfold U₁' Marlin.tithe; positivity
  let v₁ β := (F.scout Y E).pair.strong t β; let w':= Time.forecastK (a) m F.scout x
  have hv : inBand t x:= by rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in hx
  have heq : w'=v₁ x:= by unfold w' Time.forecastK; rw [PriceCompiler.beta_eq A.B.valid]
  have hb : 0≤ w'/8:= by
     have hz: 1 ≤ max 1 (F.scout Y E).coeff := le_max_left ..
     rw [heq]; unfold v₁ Payments.Pairing.strong Time.Forecast.pair; dsimp only; positivity
  have hp: U₁'≤t^( -(1/8:ℝ)):= (bless R Q A F h hk).2.2.1.curtain
  obtain ⟨b,hR⟩:= (F.inn.terms.allot _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)|>.2.2.1) x hv (w'/8) U₁' hb hh' (by rw [heq]) hp
  have ht i:= (show Trio.Tidy (V) (H.softer i) (Z.logarithm i) from Marlin.estateP (Beam.marquee K V) D★ (2*D★) (linger (Z' j) Op j Ξ Γ) (ornament ℓ (w j)) PP (fun x'=>(hY x').1) i)
  let f':=Marlin.tract c t' ∘ Marlin.leanU c
  have hε : Mallow.Vapor H Z (raiser V) U₁':= by
     refine ⟨fun i=>(ht i).uses, fun i v hi=> ?_, fun i=>(ht i).invariant,fun i=>(ht i).borel, f',Marlin.caps (Beam.marquee K V) D★ (2*D★) (V) t' hT ?_,?_⟩
     · by_contra hZK
       exact Marlin.failedP (Beam.marquee K V) D★ (2*D★) _ _ _ (fun i=>(hY i).2.1) i v hZK hi
     · intro i; unfold coverTicket; apply Nat.cast_le.mpr; apply le_trans (Trio.scaleMeters G0 B (V).B_pos i _ le_rfl); rw [two_mul]
     intro i U
     exact Marlin.softly (linger (Z' j) Op j Ξ Γ) PP t' (fun i=>(hY i).2.2) (ornament ℓ (w j)) i U
  have hp : Payments.Rates (V).B w' (w'/8) U₁' b := by
     change Payments.Rates B w' (w'/8) _ _; rw [heq] at hR ⊢; exact hR
  exact ⟨(KLink.together (KLink.together (show KLink V X0 (W0/8) (One+1) (raiser V) (H.pours Z) (w'/8) ((raiser V).supportExponent+1) from .geom rfl rfl rfl rfl le_rfl le_rfl) (.harvest (Marlin.hak H) hε hp)) (.geom rfl rfl rfl rfl le_rfl le_rfl))⟩
include K
lemma joint_invested (hA: ∀ᶠ z' in atTop, propume R Q A F hk X' u x K c₁ z') : ∃ (D'':Listing G c)(Zℓ:Collection.Source G c)(ℓ₀:ℝ), Collection.Local D'' (V) Zℓ St W0 ∧ Nonempty (Costs (D''.read Zℓ) W0 One) ∧ (Sℓ).push x U.eval= fun V₀=>sublet R₁ D'' Zℓ MNew (s) V x Γ ℓ₀ V₀:= by
 let s':= Classical.choice (Tree.select (Sℓ).ratio (Sℓ).patch.odd_side); let Vmark:= J -- J Suite not included
 obtain ⟨j,hj⟩:= (hA.and (petals R Q A F h g0 hm hk X' hh u x hx K hz hs J hG)).exists; obtain ⟨b,hε⟩:= hj; let U' := stash (Z' j) Op V Ξ Γ MNew ℓ D★ (w j) j; let H:=poursP (V) U₀ U'; let v:= Song.weighty K Op s'; let f:= Carillon.Lum (Z' j) Op Ξ Γ MNew j 0 (1:Config G c); have hΓ:= computes R Q A F h g0 hm hk X' hh u x hx K hz hs J c₁ j hu he hG
 refine ⟨ T0, H,v-f, ?_, healing R Q A F h g0 hm hk X' hh u x hx K hz hs J c₁ j hu he hG, funext fun v₁=> ?_ ⟩
 · have hh:Collection.Local (T0) V H (v'+turnFee V*Cap.footprint G L y s k G0 V) W0:= Carillon.mentor (Z' j) Op V Ξ Γ MNew ℓ D★ (w j) (k:=j) hΓ b hε; obtain ⟨z',hv,hX⟩:=hh.cheap; exact {hh with cheap:=⟨z',hv,fun i=>budget_loosen (hX i) ((bless R Q A F h hk).2.2.1.middle)⟩}
 obtain ⟨Dξ,d,vh,p₀,b',t',s₁,s₂,w₀,i,n₁,K₀,hK⟩:= Shop.appointed A F h.formal.ladder u hm K; have he: (V).order ≤(s).order:= (zones R Q A F h).2.1.2.1.le; have h1:= applies R Q A F h hm hk X' hh u x hx K hz hs s' he K₀ v₁;
 have hm' := (K.laws.data.room.buys); have hB:= paint R Q A F h g0 hm hk X' hh x hx (show 4 ≤ c.val from (by omega)); let p':= V; have hb' := Carillon.value (k:=j) (Z' j) Op V Ξ Γ MNew ℓ D★ (w j) (guidance R Q A F h hm hk X' hh u x hx K hz hs s') hB.2.1 hB.1 hΓ b v₁ x (Song.weighty K Op s') 0; change (Sℓ).push x U.eval v₁ = _; rw [hs] at h1; rw [h1]; refine hb'.trans ?_ ; have he:(s).clip=(p).clip:= congr_arg RG.Stage.clip (params_eq A.B.valid m).symm; rw [sublet, Rosary.Guard.portal,hallelujah, earlyValue, he]; -- track associativity.Same.
 change (_*Real.exp _ * Real.exp _)* Real.exp _=_; rw [mul_assoc, mul_assoc,← Real.exp_add,← Real.exp_add]; -- may wrong he mapping
 congr 2; rw [show (Pane.orchestra A N u).down=(A.B.kin.path N m) from rfl, show (Pane.orchestra A N u).low=(A.B.a.params m).clip from rfl]; ring
end WheelP
end YM.AllOrder.Transit
