import YM.AllOrder.Transit.Picnic
import YM.AllOrder.Floe.Relay
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
-- Works to retain at ALL scales. Demand Kernel.After all-in. Not θ. Also preserves startup step needs.Rebuild.Boost.H.F.A. α budgets.
structure Pass : Prop where
    tour : Tour F.shape R Q F.v F.prices F.t F.span F.recordP F.scout (wind F.menu) A.delay
    formal : Step.PlanV.Spec R Q A F
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
include h
lemma gleam:Noon F.shape R Q F.v F.prices F.t F.span F.recordP F.scout (wind F.menu) Y E y:=h.tour.actors _ _ _ (A.B.valid.pays m) (step_paid A.B.a m)
lemma zones : (V).B=radiusB y ∧ Time.Same s V ∧ Time.Same (C Y) W ∧ (V).threshold=temp y ∧ (W).threshold=temp (betaF G y L) ∧ (W).B=radiusB t ∧ (W).B≤2* (V).B ∧ 1 < t:=by
 have hv: A.B.a.clock.hatBeta (m+1)=betaF G y L:= PriceCompiler.beta_eq A.B.valid m; rw [← params_eq A.B.valid m, ← params_eq A.B.valid (m+1), ← hv]; refine ⟨rfl,⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩,rfl,rfl,rfl,?_,A.B.a.fits.delayed _⟩; refine ?_; change radiusB ((A.B.a).clock.hatBeta (m+1))≤2*radiusB y; rw [hv]; exact (gleam R Q A F h).sizing -- tool
local notation "z"=> Burn.horizon k
variable (g0:G.Simple)(hm:m<N)(hk:Burn.horizon k+2≤ A.B.a.clock.J m)
lemma wide : Loft V (A.B.a.S.side m n):= by
 let E':= E; let N:= A.B.a.S.side m n; let u:=Y; let d:= A.delay; let v:=(V).B; have hv:1≤ v:=(V).B_pos; obtain ⟨ht,he⟩:=h.tour.volumes (u); have hh: d.shells u * (1+v+(W).B)^d.growth u ≤ N.val:= A.B.valid.volume m n; refine ⟨?_,?_⟩; · refine le_trans (Nat.mul_le_mul (show _≤ d.shells u from ht) ?_) hh; change v^2≤_; exact le_trans (Nat.pow_le_pow_right hv he) (by gcongr; omega)
 exact Return.enough_room A.B m n
include hk
lemma fitsB : Glimmer F.shape R Q Y E k y:= (gleam R Q A F (m:=m) h).pearl _ (by unfold horizon at hk; omega)
local notation "G0"=> Shop.parking (Shop.tall E) ((T).halo)
local notation "Δ0"=> 1+cloak D (Y)
local notation "Θ"=> (Tour) -- unused
local notation "δ"=> (A.B.a.params m|>.width)
lemma bless : Width (Rosary.pearl V) (p).clip δ ∧ 4*(horizon k+4)≤ (V).B ∧HorizonW G L y s k G0 V ∧ (∀ c:ℝ,Near y c→ PostP.C' V G k c y≤fee1 G L y)∧((V).threshold≤2*Pressure.fiery G y L→∀ β b Λ,|β| ≤4*t→|b|≤ Δ0 → 0≤ Λ→ Λ ≤ ConnectedActivityE6.loopBill G L y → octaveNeed G V (p).clip δ (p).paths Λ β b ≤ 2*fee1 G L y ∧ Real.exp (-(δ/4)*↑((V).B)) * octaveNeed G V (p).clip δ (p).paths Λ β b ≤pen G L k y 0):= by rw [params_eq A.B.valid m]; exact (fitsB R Q A F h hk|>.post).predicts V ((zones R Q A F h).2.1) rfl rfl
lemma capacitor : Burn.Capacity G W (t) k:= by
 obtain ⟨hx,hv,ht,hp,ht',hs,hh⟩:=zones R Q A F (m:=m) h; exact (fitsB R Q A F h hk).lasso _ ht ht' hs
section model
variable (X': Card D R (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (A.B.a.clock.adm (m+1)) (Burn.horizon k))(hh:Journey R A (m:=m) (N:=N) X') -- syntax
local notation "Ω"=> litP R A Q hk X'
abbrev lead (U:Card D R Y E (A.B.a.clock.adm _) (z)):Layout G:= (litP R A Q hk U).laid U
local notation "Plead"=> lead R Q A hk X'
local notation "W'"=> (C Y)
local notation "fφ"=>R.pre z Y
include hh
lemma LegalP : ∀ i∈Age.scope (z+2), Quoted (X'.extra i) (fφ i) (authority z i (strengthP t)):= by
 intro i hi; have h:= X'.quote i hi; rw [hh.books.fisc] at h; exact h
lemma LegalQ :∀ i∈Age.scope (z+2),Quoted (Plead i) (R.pre z E i) (authority z i (strengthP y)):= by
 intro i hi; exact (PlanV.readable R A F Q h.formal X' hk hh).1 i hi -- implicit
end model
end WheelP
end YM.AllOrder.Transit
