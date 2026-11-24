import YM.Qlocal.Moonset.Invitations
import YM.Qlocal.Moonset.Exchequer
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Actual
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open Further.PhysicalPeriodLimitF933 PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
open Program Program.Camp Program.Certificate
variable {Ω V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge} {m k p N j k' z n l v : ℕ} {δ r θ u E C ℓ: ℝ}
open Primitives.TwoWave Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open AllOrder Ker Ker.Start Haiku Haiku.Coat Fire Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money
open Work.G05 Kinetic.Port Kinetic Binding
open Comparison.RG02.Bulk
open Org Floe Pace Step.PlanV
namespace Season
variable (X:Run G)
set_option quotPrecheck false
local notation "W"=> X.metals
local notation "D"=> X.rolls
local notation "A"=> X.alloy
local notation "C"=> X.family
local notation "Y"=> RunFormalChain.fromRun X
local notation "a"=> X.alloy.B.a
local notation "K"=> X.metals.p.kernel
local notation "J"=> X.alloy.B.a.clock.J (m+1)
local notation "J'"=> X.alloy.B.a.clock.J m
local notation "t₀"=> X.alloy.B.a.clock.adm (m+1)
local notation "κ"=> X.metals.p.profile
local notation "S"=> (a).clock.op m p
local notation "c"=> (a).S.side m p
local notation "f"=> (a).S.side (m+1) p
local notation "k₀"=> Burn.horizon k
local notation "Ω★"=> Age.scope (Burn.horizon k+2)
variable (R: Roots (G:=G) X.metals.p.profile X.metals.K X.metals.p.kernel)(Q:R.Tab X.rolls)
local notation "I"=> Card D R J J' t₀ k₀
open Squall Squall.Lumber Skating Skating.Rune
open Dredge Quipu Quipu.Sonnet Tern Quipu.Eluder Quipu.Eluder.Incline Quipu.Eluder.Incline.Bookworm
open Gauges Gauge Booth BoothRent Moonset PostDebt Calendars Calendars.Banknote
variable (η ζ:ℕ→ℝ)(H:ℕ→ℕ)
variable (w:ℕ→Layout G)(Γ: ℕ→ Pace.Coin) (g:G.Simple) (hK:TicketP X.alloy X.kit R Q)
variable {x:(i:ℕ)→RG.Rep G ((X.alloy).B.a.S.side i p)}
local notation "F"=> X.kit
local notation "D₀"=> StepStages J J'
variable {r0 qd:ℕ} [Fintype V][Nonempty V] (ξ: V→ℕ)(b i:ℕ) (hm:m<N)
local notation "β"=> (X.T.history N p (m+1)).beta
local notation "Λ"=> (Teller)
local notation "Π"=> (A).B.a.S.oneStep m p |>.exact_size
variable (P0: Studio X R Q η ζ H w Γ hK ξ b i hm r0 k z B qd)
local notation "H★"=> Boreal.Plans X R Q x hm P0.base ξ b qd r0 P0.hardware P0.credentials hK P0.tintinn
variable (hp : Metre X.alloy X.kit X.T w Γ z N p k x) (ht:z   ≤   m)
local notation "FF"=> litP R A Q (P0).hdr (P0).base
local notation "Aq"=> P0.base
local notation "δ'"=> (A).B.a.clock.hatBeta m
local notation "βo"=> (X.T.history N p m).beta
local notation "Yg"=> (A).B.a.clock.hatBeta (m+1)
local notation "X'"=> (X).family.path
open Wheel PostDebt
open Parabola Reckoner
variable (T:Ray B)(hT:Rental T){Ω:Type} (Z': Ω→Dredge.Sail V X.rolls R (X.alloy.B.a.clock.J (m+1)) (X.alloy.B.a.clock.J m) (Burn.horizon k) i (X.alloy.B.a.clock.adm (m+1)) B ξ qd b)
variable (s:V→Support (X.family.side (m+1) p))(o:V→Site (X.family.side (m+1) p))(v': Ω→Senses B→ℝ)(hq: Boreal.ModelProof X R hm ξ b qd P0.tintinn Z' v' T o)
    (hQ: Moonset.StationFee R Q (fun i=>2*ζ i) X.alloy.delay)
    (hv: ∀ i:V,s i⊆ Uplink.habitat (X.family.side (m+1) p) (X.alloy.B.a.clock.hatBeta (m+1)) (o i))
namespace Exchequer
open Moonset.Rooms Studio
variable (Xo:(m:ℕ)→ V→Site (X.family.side m p)) (Xs:(m:ℕ)→V→ Support (X.family.side m p))
    (Θ: ∀ m:ℕ, z   ≤   m → ∀ hm:m<N, Studio X R Q η ζ H w Γ hK ξ b i hm r0 k z B qd)
/-!
# Schedules for a finite marked census

For a fixed census on `Fin n`, `pledged` obtains `Fees` and a schedule for
every cutoff `N ≥ z` on an eventual tail of starting levels `z`. It uses the
station fee, the `Woken` data, the per-mask warrants, and the stated bounds
on the census size and order.

`Calm.provide` constructs a gallery and a delivered wallet for the supplied
stanzas, supports and amplitudes. At the initial level its interpretation is
the product of the rendered polynomial and the original path density.
`purchased` selects a run, a grant and a camp with the schedules for the
admissible finite censuses.
-/
variable (Z0: ∀ (z N:ℕ),Burn.horizon k+2  ≤  X.alloy.B.a.clock.J z→ z  ≤  N → Woken X R Q η ζ H hK k z N)
local notation "p0"=> z
local notation "ℊ"=> (a).clock.J
include g hQ Z0
variable (δ:ℝ)(hH:Tendsto H atTop atTop)(hζ:Tendsto ζ atTop (𝓝 0))
include hζ hH
set_option maxHeartbeats 1500000
lemma pledged (B : Marker.Census (Fin n)) (g':Fin n→ℕ)(r:ℕ) (hc:0<n)(hr:n  ≤  r0) (hf : qd  ≤  Burn.horizon k+1)(hU:δ  ≤  qd+1)(ht:0<δ) (hi:i  ≤  b)(hx:2  ≤  i)(hZ:∀ s:Senses B,warrant qd s g' i): ∀ᶠ z in atTop, Fees X B ζ H z qd r δ ∧ ∀ [Nonempty (Fin n)] (N:ℕ),z  ≤  N→ Exchequer.ScheduleOf X R Q η ζ H hK g' b i r0 k qd N z B δ := by
 have hz:= (a).fits.deep; let M' := max (Fintype.card (Senses B)) (Fintype.card (Gauges.Atlas.Notice B)); let L:= ∑ s:Senses B,Lagger.dues g' s.val; have hN : Nonempty (Fin n):= ⟨⟨0,hc⟩⟩
 have ht': ∀ᶠ x in atTop,∀ i,g' i  ≤  ℊ x:= eventually_all.mpr (fun t:Fin n=> hz.eventually_ge_atTop _)
 filter_upwards [Fees.chosen X ζ H g B r qd hU ht hH hζ, hz.eventually_ge_atTop (Burn.horizon k+2),hz.eventually_ge_atTop b,hz.eventually_ge_atTop L, hz.eventually_ge_atTop M', ht',hz.eventually_ge_atTop r0] with z ht hk hb he hV hW hR; refine ⟨ht, fun N hN'=>?_⟩; apply Exchequer.compass X R Q η ζ H hK b i hQ δ L M' (Z0 z N hk hN') B g' hc hr hx ?_ hk hW hR hZ; exact ⟨le_max_left ..,le_max_right ..,(fun s=> Finset.single_le_sum («f»:=fun s:Senses B=> Lagger.dues g' s.val) (fun _ _=>Nat.zero_le _) (Finset.mem_univ _)),hf,he,hV,hb,hi⟩
omit hQ g hζ hH Z0
lemma enough (α:Type)[DecidableEq α][Fintype α] (B : Marker.Census α) (g':α→ℕ) (qd:ℕ) : ∀ᶠ i in atTop,2  ≤  i∧∀ s:Senses B,warrant qd s g' i:= (eventually_ge_atTop 2).and (eventually_all.mpr fun s=> eventually_ge_atTop _)
variable (hc: z ≤ j) (he:j  ≤  N) (u':ℝ)(hCalm: Calm X R Q η ζ H hK ξ b i z N k r0 qd w Γ B Θ δ)
variable [Nonempty Ω] (Y0:Ω→ Stanza B G ξ qd)(Z:∀ i,(Stanza.son (Y0 i) b).Decision)(v0:Ω→ Senses B→ℝ) (hY:∀ t,(Stanza.son (Y0 t) b).Allows (Prior.yard R (Burn.horizon k) i (X.alloy.B.a.clock.J j)) 1)
variable (hZ: ∀ v:V,Xo j v∈ Xs j v) (hV:∀ i:V,Xs j i ⊆ Uplink.habitat (X.family.side j p) (X.alloy.B.a.clock.hatBeta j) (Xo j i)) (h0:∀ x s, T (s:Senses B).val* |v0 x s|  ≤ 1)
local notation "bH"=> Studio.herald X ξ b Xo Xs Y0 Z v0 (x:=x) j
include hT hY h0 hZ hV hCalm hp hc
lemma Calm.provide (hO:Studio.Pinned X Xo Xs z j)(hα:Studio.Charged X ζ u' z H (p:=qd)) : ∃ (p₁:Studio.Shell X R ξ b i T Xo Xs u' j bH (k:=k) (j:=j) (x:=x)) (Q0 : (j:ℕ) →Wallet Ω (Xo j) (x j) B ξ qd b), Gallery X R Q η ζ H w Γ hK ξ b i T Xo Xs Θ u' Q0 bH z p₁ le_rfl he ∧ Delivered X ζ H ξ b T Xo u' Q0 z (N:=N) (j:=j) (δ:=δ) ∧ ∀ (t:Ω)(u₀:Config G (X.family.side j p)), Studio.interpretation (N:=N) X ξ b j bH t u₀ = Poly.pass ( (bH).render (Stores.till (X.alloy.B.a.clock.hatBeta j)) (Coat.gStep (X.family.path.β N p j)) t u₀)* Poly.bead B (((X.family.path.rep N p j).eval u₀):ℂ):=by
 have h':= Studio.pre_chord X R ξ b i T hT Xo Xs Y0 Z v0 u' (x:=x) hY hZ hV h0 hα.positive hα.small; obtain ⟨U,hU,hw⟩:= hCalm.action p x hp j hc he Ω Xo Xs bH T u' hα hO h'; exact ⟨h',_,hU,hw,fun u v=>Studio.begin_epoch X w Γ ξ b hp Xo Xs Y0 Z v0 hc he hZ u v⟩
omit hCalm hc hT hY h0 hZ hV hp
include g
open Prefect
variable (Lh:ℕ→ℕ)
local notation "ϕ"=> Schedule.tandem (Prefect.Course η H ζ) (Spending (fun i=>2*ζ i))
lemma purchased (d:ℝ) (he:0<d)(hp:∀ i,0 < η i)(hr:∀ i,0<ζ i)(ht:∀ i,ζ i  ≤  1/4)(hζ:Tendsto ζ atTop (𝓝 0))(hu:Tendsto H atTop atTop):∃ (X:Run G) (R: Roots (G:=G) X.metals.p.profile X.metals.K X.metals.p.kernel) (Q:R.Tab X.rolls) (hF:Grant X R Q η ζ H) (C':Camp X.kit η Lh H),
   Moonset.StationFee R Q (fun x=>2*ζ x) X.alloy.delay ∧ X.family.path.levels.clock.kernel.penalty=d ∧ C'.height=(fun i=> Lh (X.alloy.B.a.clock.J (i+1))) ∧ (∀ (k z N:ℕ), (Burn.horizon k)+2 ≤ X.alloy.B.a.clock.J z → z ≤  N → BoothRent.Woken X R Q η ζ H hF.authority.resource k z N) ∧
      ∀ (k n r0 qd b i r:ℕ)(B:Marker.Census (Fin n)) (g': Fin n→ℕ)(δ:ℝ), 0 < n → n  ≤  r0 → qd  ≤  Burn.horizon k+1 → δ  ≤  qd+1 → 0<δ→i  ≤  b→2  ≤  i→(∀ s:Senses B,warrant qd s g' i) → ∀ᶠ z in atTop, Fees X B ζ H z qd r δ ∧∀ [Nonempty (Fin n)] (N:ℕ), z  ≤  N → Exchequer.ScheduleOf X R Q η ζ H hF.authority.resource g' b i r0 k qd N z B δ:=by
 have hf: Schedule.Obtainable (G:=G) (Schedule.berth (ϕ)):= Schedule.all_chances g _ (Schedule.Prospecting.twin (Prefect.contracts η H ζ hp hr ht) (Moonset.invoices _ (fun i=>mul_pos zero_lt_two (hr i)))); obtain ⟨Xr,hM,hc,hK⟩:= Run.rampK g ((hf.also Calendars.Uplink.preferred).also (Program.sold η Lh H g hp)) d he; obtain ⟨⟨X0,Y',hF,hP,hξ,hq⟩,h_B⟩:= hc
 let hT: Account η H ζ Xr.metals Xr.rolls Xr.alloy Xr.kit X0 Y':= (show Prefect.Plateau _ _ _ _ _ _ _ from hξ).parent; let hG:Grant Xr X0 Y' η ζ H:=⟨⟨hF,hP,hT⟩,hξ,h_B⟩; obtain ⟨Qw,hQ⟩:= Program.supplier Xr.kit η Lh H hK (d:=fun m=>Lh (Xr.alloy.B.a.clock.J (m+1))) (fun i=>le_refl _); have hA(k z N:ℕ)(hX:Burn.horizon k+2  ≤  Xr.alloy.B.a.clock.J z)(hY:z ≤ N):Woken Xr X0 Y' η ζ H hG.authority.resource k z N:= BoothRent.breaking Xr X0 Y' η ζ H g hF hG hX hY; exact ⟨Xr,X0,Y',hG,Qw,hq,hM,hQ,hA,fun k n r0 qd b i r B g' δ hc he hf hX hz hU hY hw=> Exchequer.pledged Xr X0 Y' η ζ H g hF b i hq (hA k) δ hu hζ B g' r hc he hf hX hz hU hY hw⟩
end Exchequer
end Season
end YM.Qlocal.Actual
