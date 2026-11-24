import YM.RG05Readout.Shadows.Sink
/-!
# From authenticated tickets to earned replicated estimate

C real Family; f integral via certified trajectory/germ happens upstream.
Purchases COPY terminal charge and reference normalizations. Conditional
on `LotusNotes` and actual packet tickets; See e.g. proof `stepFirst`
which needs them on a multiplicative simultaneous rendering. Sources and
reference remain on same vacuum and propagate down authenticated tours.
No analytic power estimate assumed or derived by this port alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address Many Pressure
open Legato Bandage Next.Rank.Station Accent Marker Menu Ac OPE
open GridApprox.Nil Extra.Trajectories Extra.Multi
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N n b m p d:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ} {x e E a r y z:ℝ}
set_option quotPrecheck false
variable (h:C.Makes){V:Sight C d p}{S:Emblems C d}
local notation "Z!"=> C.path.levels
local notation "R₀"=> C.path.rep N p
local notation "Ω"=> C.path.levels.clock.op
local notation "Z₀"=> C.path.levels.budget
variable (hw:Awake D B b d)(hv:Spine D B h b p d N V S) (hc:Cater C D) (hs: Storage C D)
variable (F:Goods G (C.side (n+1) p))(w:PulseC)
variable {H:∀ i:ℕ,Tape G (C.side i p)} {Y:ℕ→Palette C d} (ht: Signature C p b n N d h D V (amplitude C n N p d w F) e Y H)
    (hm:b ≤ n)(hN:n<N)
section
variable {I:ℕ→Type}{J J':Type}[∀ i,DecidableEq (I i)][∀ i,Fintype (I i)] [Fintype J'] [DecidableEq J'] {R:Census J'}
    (A: Planner C p b I J) (F':∀ i,I i→Body) {G':∀ i,Census (I i)}
    (θ : J' ≃ I (n+1)× Bool)
local notation "B'" => A.narrows
local notation "ψ"=> A.supportX
local notation "Γ"=> Prod.fst ∘ θ
local notation "ε"=> Many.apron C.path.levels
local notation "v!"=> pens A θ (F' (n+1)) w
variable (f:J'→ Three G (C.side (n+1) p)) {y':∀ i, Config G (C.side i p)→Poly (G' i)}
include h hw hv ht hN hc hs hm
lemma descend (T:Config G (C.side (n+1) p)→ Poly R)(hr:0 < r)(hξ:MenuBoard (R₀ (n+1)) f T (ψ (n+1) ∘ Γ) (fun _=>r) ((Z₀ (n+1)).supportExponent-2) 1)
    (hp: LotusNotes (S:=S) (V:=V) (Y:=Y) (N:=N) (θ:=θ) F A F' f a) (hP:∀ i:I b,Cap (d+2) (F' b i) 1)(h_F: PreparedA A F' b (n+1) le_rfl)
    (ht':d+3 ≤ C.path.levels.clock.J n)(hU: ∀ i,b ≤ i→ Pin C i d)(hY: Priced d w 1)(ha:0 ≤ a)
    (hk:License (G' (n+1)) R Γ) (hO:∀ i:ℕ,b ≤ i→i ≤ n→Occupancy (ψ (i+1)) (ε i)∧ Occupancy (((Ω i p).ratio.parent) ∘ ψ (i+1)) (ε i))
    (hg:∀ i:ℕ,b ≤ i→i < n→ Drake (G' (i+1)) (Z₀ i).B (((Ω i p).ratio.parent) ∘ ψ (i+1)))
    (hy:y' (n+1) = fun U=> feed v! hk (T U)) (hR:Replay A (fun _=>d) (le_refl b) (n+1) y' N) :
       let E:= safe C d n e r a; 0<E∧ ∀ M s, (∫ U,(y' b U).part s∂prior G _)=(Wilson.partition G (C.side N p) (C.beta N p):ℂ)*M → ‖M‖*(focus C E n b)^s.val.card ≤ Real.exp ((Fintype.card (Site (C.side b p)):ℝ)* Vac.treasury C.path.levels b+ Fintype.card (I b)*(2*salary C b d+2)):=by
    intro E; obtain ⟨q,hq⟩:= hR.downhill (V:=I) n hm (n.lt_succ_self)
    obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩:=buys (C:=C) (n:=n) (d:=d) (show 0 ≤ e from by linarith only [ht.pays, size_ge (Y n)]) hr ha
    refine ⟨h4, fun M s he=>?_⟩
    have h : Aura (S:=S) (V:=V) H Y A F' (N:=N) (n:=n) (G':=G') n (y' n) E ((Z₀ n).supportExponent):=by
       rw [hq,hy]; exact stepFirst ‹C.Makes› hw hv hc F w ht hm hN (hU b le_rfl|>.lit.1) A F' θ f _ hξ hp (cap_lives A (fun _=>d) F' (le_refl b) hm n.le_succ h_F hP) (h_F n hm n.lt_succ_self) ht' hY ha h4 hk q (hO n hm le_rfl).2 (hO n hm le_rfl).1 h1 h2 h3 h5 h6
    have hP':= dawns ‹C.Makes› hw hv A F' (Y:=Y) ht.rolls hs hm hN.le (fun i he hi=> h_F i he (hi.trans n.lt_succ_self)) hP h h4 h7 (fun i hk hi=> hO i hk hi.le) ⟨fun i hk hi=> hR.downhill (V:=I) i hk (hi.trans n.lt_succ_self)⟩ hg hU b le_rfl hm
    exact Shadow.terminal ‹C.Makes› hw A F' hm hN hP hP' h4 s M he
end
-- reference size also shows USING model-ish analytic report bounds would buy apertures at physical scale
end YM.RG05Readout.Shadow
