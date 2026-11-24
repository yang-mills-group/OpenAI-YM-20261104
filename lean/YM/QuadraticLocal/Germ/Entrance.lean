import YM.QuadraticLocal.Germ.Trajectory
import YM.QuadraticLocal.Germ.Focal
/-!
# APPLICATION I — full marked trajectory theorem for palette/coupling admission
 on a CLOSE-Epoch (`ℝ`-budget protocol real and held-slot complex genuine lighting).

 Provides all orientation, test location credentials and affordability for RE-PUSHING.
 Actual K partner power beyond weak divided costs shown on projected Stage masks at EVERY level
 including after marked time window at restored weights, without price equivalence from another
 vacuum. Uses Passport strongly-packed budgets.Tier.Stage.Released (`growth` this path) AND
 construction Station. Projection to x.Phys.All mask conditions exact by proof.

 Launch all mask/support assertions kept on compact regulator; callers of wrapping/stencil bounds
 for analytic packets can request also their genuine support to be registered (name coding and
 momentum lifts separately, not implied by this statement). Budget Certificate stronger than
 `acak.factorial FullBudget` at assembly; publication retains declared forced labels. At moment
 for sharp qlocal this proves *the forced-output* along unmarked history across finite marked
 protocols (fixed loan K, not the arbitrary W-mark path Ward result or aligned analytic kernels),
 not E qelt except by special classes later. Push procedures apply all values, sup inside.
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
local notation "P'"=> Ψ i
local notation "H"=> Opera.Guide R.alloy.B (R.kit.shape)
local notation "wa"=> Time.forecastK S i (R.kit).scout (P).beta
local notation "wp"=> Time.quoteHard S i (R.kit).book (P).beta
local notation "y₀"=> Willow.haloSlack (X).B
local notation "Γ'"=> R.T.history N n
open Integration.LocalComparison
open Marker
namespace Expedition
open Display.Lens Relay Affinity.Smalt PaceR
variable {V:Type}[Fintype V][Nonempty V][DecidableEq V]{J:Marker.Census V}
variable {ε:ℝ} {u:ℕ}
open ComparisonDensity.Address
variable (Ad:V→Orbit)
local notation "M"=> fun i=>(Ad i).Mood
local notation "Tax"=> Display.Lens.portion Ad
variable (K:∀ i,Submodule ℂ (Ad i).Mood)
variable (w:V→ℝ) (hw:∀ i,0<w i)
variable (o:(i:ℕ)→ V→Site (R.family.side i n))
variable (T:(i:ℕ)→ V→Support (R.family.side i n))
variable (hr:∀ i,m ≤ i → i < b → o i=(R.family.path.levels.clock.op i n).ratio.parent ∘ o (i+1))
variable (he:∀ i,m ≤ i → i < b → T i=(fun v=> (T (i+1) v).image (R.family.path.levels.clock.op i n).ratio.parent))
variable (Eₜ:Estate (Affinity.Full (E:=fun i=>(Ad i).Mood)) (o b) (Ψ b) J)
variable (hz:∀ i, o b i∈ T b i)(hb:b≤N)
local notation "α"=> Affinity.Full (E:=M)
local notation "E!"=> fun i=> Estate α (o i) (Ψ i) J
local notation "toll"=>fun i=> Stoop.radius w (roof R i b)
variable (hX:Affinity.Adult (T b) K Eₜ.canvas) (hT:(dict (Display.Lens.portion Ad) Eₜ).canvas.Pays w ((Ψ b).p.supportExponent) 1 1)
variable (D₀:∀ i,m ≤ i → i ≤ b → Estate (Affinity.Full (E:=fun i=>(Ad i).Mood)) (o i) (Ψ i) J)
set_option quotPrecheck false
local notation "TX"=> (fun i hi hb=> dict Tax (D₀ i hi hb))
local notation "B!"=> Display.Lens.theater
-- carry stages receive Aff.MaskOrientation.Region
structure Polished (ε:ℝ)(u:ℕ)(D₁:∀ i,m ≤ i→ i≤ b→ Estate (Affinity.Full (E:=fun i=>(Ad i).Mood)) (o i) (Ψ i) J) : Prop where
    journey : TreeHouse R (N:=N) Ψ (Display.Lens.portion Ad) K w o T Eₜ m D₁
    era : Stories R π Γ Ψ v ε u hb (fun i hi hk=> dict (Display.Lens.portion Ad) (D₁ i hi hk)) (w:=w) (J:=J)
    many i (hi:m≤ i)(hh:i≤b): Integration.LocalComparison.Multilinear Ad (B! Ad (D₁ i hi hh).canvas)
    stores i (hi:m≤ i)(hh:i≤b): RetainsDeclared (Display.Lens.stands Ad (D₁ i hi hh).canvas (T i)) (B! Ad (D₁ i hi hh).canvas) (T i)
    leaps i (hi:m≤ i)(hh:i≤ b): (∀ U x, ((B! Ad (D₁ i hi hh).canvas).leaf x).density U=(D₁ i hi hh).canvas.density x U)
    stations i (hi:m≤ i)(hh:i<b): Nonempty (FullBudget (Ψ i).p (Integration.LocalComparison.pullback (testInclusion Ad) (B! Ad (D₁ i hi hh.le).canvas)) w (forcedDivisor R.family i) (4*(Φ b)^ε) ((Φ b)^(-(u:ℝ))))
    invitations i (hi:m≤ i)(hh:i<b): ExactStep (avatar R π Γ Ψ v (Nat.le_succ_of_le hi) (show i+1≤N from le_trans hh hb)) (avatar R π Γ Ψ v hi (le_trans hh.le hb)) (o (i+1)) (o i) (B! Ad (D₁ (i+1) (Nat.le_succ_of_le hi) hh).canvas) (B! Ad (D₁ i hi hh.le).canvas)
local notation "Y'"=> TreeHouse R (N:=N) Ψ Tax K w o T Eₜ m D₀
variable (ε u)
include K hr he hz
omit K [Nonempty V] [Fintype V] [DecidableEq V] in
lemma heads (hi:m ≤ i)(hi':i≤b) : ∀ y:V,o i y∈ T i y:= by
    induction hi' using Nat.decreasingInduction with
    | self=> exact hz
    | of_succ i hx ih=> intro y; rw [hr _ hi hx, he _ hi hx]; exact mem_image_of_mem _ (ih (Nat.le_succ_of_le hi) y)
include hw v hb
lemma attach (hL:Y')(hS:Stories R π Γ Ψ v ε u hb TX (w:=w) (J:=J)): Polished R π Γ Ψ v Ad K w o T Eₜ hb ε u D₀:=by
    have he' (i:ℕ) (hi:m ≤ i)(hh:i≤ b) : Prospects ((D₀ i hi hh).canvas) := prospect (D₀ i hi hh).canvas (adopts Ad) (Affinity.Smalt.exfil _ (hL.carries i hi hh)) (hL.bills i hi hh) (Ψ i).p.exponent_pos.le (health w hw R b i)
    have hX0 i (hi:m ≤ i)(hh:i≤ b)(x) : ((B! Ad (D₀ i hi hh).canvas).leaf x).density= (D₀ i hi hh).canvas.density x:= Display.Focal.organized _ x ( (he' i hi hh).lights x · ) -- type signature organization h
    refine ⟨hL,hS,fun i hi hh=>Display.Lens.print Ad _ _ K (hL.carries i hi hh), fun i hi hh=> Display.Lens.retention Ad _ _ K (hL.carries i hi hh) (heads R o T hr he hz hi hh),fun i hi hh U x=> congr_fun (hX0 i hi hh x) U, fun i hi hh=> Display.Lens.supplies Ad _ (hS.full i hi hh), fun i hi hh=>?_⟩
    refine ⟨ fun v=> congr_fun (hr i hi hh).symm v, fun x=>?_⟩; exact (congr_arg (Integration.LocalComparison.actualPush (Z) N n i («R»:=J)) (hX0 _ (Nat.le_succ_of_le hi) hh x)).trans ((hL.tall i hi hh x).trans (hX0 i hi hh.le x).symm)
omit hw v hb K hr he hz
end Expedition
-- public.Final
open Expedition
include g h K₀
variable (mK: ℕ) (a:ℝ)(ha:0≤a) (ε:ℝ)(hv:0<ε)
include ha hv
open ComparisonDensity.Address PaceR Relay
lemma realm (d' u' u:ℕ): ∀ᶠ b in atTop,∀ m ≤ b, Close R d' a m b→∀ N:ℕ, ∀ _ : b≤N,∀ k:ℕ,Burn.horizon k+2≤ (S).clock.J m →∃ π Γ, Step.PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ ∧ ∀ n:ℕ, ∃ Ψ:(i:ℕ)→RG.Rep G (R.family.side i n),∃ v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ, ∀ (V:Type)[Fintype V][Nonempty V][DecidableEq V] (J:Marker.Census V), (∀ i:J.Mode,i.val.card ≤ u') → ∀ (Ad:V→ ComparisonDensity.Address.Orbit)(K: ∀ i,Submodule ℂ (Ad i).Mood) (w:V→ℝ) (o:(j:ℕ)→V→ Site (R.family.side j n))(T:(i:ℕ)→ V→Support (R.family.side i n)), (∀ i,0<w i)→(∀ i,m ≤ i → i < b → o i=(R.family.path.levels.clock.op i n).ratio.parent ∘ o (i+1)) → (∀ i,m ≤ i → i < b → T i=fun v=>(T (i+1) v).image (R.family.path.levels.clock.op i n).ratio.parent) → (∀ v,o b v∈ T b v) → ∀ (Yt:Estate (Affinity.Full (E:=fun i=>(Ad i).Mood)) (o b) (Ψ b) J), Affinity.Adult (T b) K Yt.canvas → (Relay.dict (Display.Lens.portion Ad) Yt).canvas.Pays w (Ψ b).p.supportExponent 1 1 → ∃ D₁:∀ i,m ≤ i → i ≤ b→Estate (Affinity.Full (E:=fun i=>(Ad i).Mood)) (o i) (Ψ i) J, Polished R π Γ Ψ v Ad K w o T Yt (show b≤N from by assumption) ε u D₁:=by
    filter_upwards [on_tail R g d' a u', PaceR.quarters R g h a ha d' u' u ε hv] with b hB hP m hm hC N hb k hk
    obtain ⟨π,Γ,hπ,hZ⟩:= shipped R g h hk D Q K₀ (hm.trans hb); refine ⟨π,Γ,hπ,fun n=>?_⟩
    obtain ⟨Ψ,v⟩:= hZ n; refine ⟨Ψ,v,fun Θ _ _ _ J hJ Ad K w o T hw hr he hz Yt hX hY=>?_⟩; set Ax:= Display.Lens.portion Ad with hAx; haveI : Nonempty (Affinity.Wallet Ax):=by rw [hAx]; infer_instance
    obtain ⟨T',hT⟩:= Relay.lives R h D Q π Γ Ψ v K₀ (Display.Lens.portion Ad) K (Display.Lens.adopts Ad) (Display.Lens.spin Ad) hJ w hw o T hr he Yt hX hY (hB m hm hC) hb le_rfl hm; have he':= Relay.utter R (N:=N) Ψ _ _ w o T Yt T' hT; exact ⟨T',Expedition.attach R π Γ Ψ v ε u Ad K w hw o T hr he Yt hz hb T' hT (Stories.ready R h π Γ Ψ v hw he' hr (hP m hm hC k N π Γ n Ψ v hb _ Θ o J w _ _ hw hJ he') hb)⟩ -- args
end YM.QuadraticLocal.Advent
