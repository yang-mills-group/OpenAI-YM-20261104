import YM.FVA2.InvJet
/-!
# The position scheme X before final mass/dilation-equivariant gauge

Prove the formal position-scheme correspondence. Supply one formal χ,L for all horizons from one
MS array; then ren X shape. Here still at one q, any qc.T.S by Drum.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 940000
noncomputable section
namespace YM.FVA2.Elegant
open Function Filter Set MeasureTheory PositionX
open Pert Pert.Position Maxwell Maxwell.Free PositionX.Bare.Shop PositionX.Jet
open PositionX.Ribbon PositionX.Detector PositionX.Bend
open Lattice Topology
open MS MS.Menus MS.Land MS.Theater MS.Book MS.Book.Program MS.Book.Convolve MS.Orbit MS.Tide MS.Rake
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend BoxOffice Blaze Frost ArchTurn
open PowerSeries WorldJet Counterpart Spring
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} (hg:G.Simple) {B:Booked (wings G)} (V:Warehouse G)(P: Prescription (wings G))(M:MS_Data G B)
variable (H:ExactSpin V P)(HI:Trusted P)(he: MixedStory.AllProfiles M V P)
variable (q:ℕ+)(hq:1<q.val) (μ:ℝ) {d c:ℕ}
local notation "Y"=> V.F
local notation "ℙ"=> BoxOffice.warehouse V
local notation "D"=>nested V.F hg ( BoxOffice.warehouse V )
local notation "𝒮"=>ms V M μ
local notation "Ξ"=>Bank V.F
local notation "κ"=> Buffer V.F
local notation "ℓ"=> lookie V.F
local notation "ψ" x=> (μ-Pond.clock q x)
-- wrappers.G.
def turns (d:ℕ) : Word (Buffer V.F d) := (D d).report ( ms V M μ d )
def dawnFrame (k d:ℕ): Word (κ d) := hall V P H HI (PertExtension.LatticePT.epsilon q k) (ψ k) d
def motion (k d:ℕ) := ( BoxOffice.warehouse V ).bank q k d
def clockM (k:ℕ): Word ℝ:= ζq P.team (ψ k)
def unglue (k d:ℕ): Word (Ξ d):= changedWorld V P H HI q k (ψ k) d
abbrev bust (k d:ℕ) := (nested V.F hg (warehouse V) d).report ( unglue V P H HI q μ k d )
def stage (k d:ℕ) := predMarket ( bust hg V P H HI q μ k d ) ( unglue V P H HI q μ k d )
def pattern (d:ℕ): Word ( Bank V.F d ) := predMarket (turns hg V M μ d) ( ms V M μ d )
abbrev uncut (k d:ℕ) := ( BoxOffice.warehouse V ).uncut hg q k d
local notation "γ"=> turns hg V M μ
local notation "t"=> pattern hg V M μ
local notation "s"=> stage hg V P H HI q μ
local notation "τ"=> unglue V P H HI q μ
local notation "𝔽"=> clockM P q μ
local notation "Δ"=>dawnFrame V P H HI q μ
local notation "Λ"=> motion V q
local notation "W"=> bust hg V P H HI q μ
local notation "x"=> uncut hg V q
local notation "F"=> (atTop:Filter ℕ)
lemma φconomic (k d:ℕ): τ k d = predMarket (Δ k d) (ren (𝔽 k) (Λ k d)):= rfl
lemma φzero (k:ℕ): light (𝔽 k):= Clock.rooted P.team _
lemma φone (k:ℕ): 𝔽 k 1=1:= Clock.bare_tangent _ _
lemma renamed (k:ℕ) (w:Word (Bank V.F d)): ren (𝔽 k) w 0=w 0:= subleading0 V (ψ k) _ _
lemma reports0 (d:ℕ) : γ d 0=0:= ( solves_only (D d) (𝒮 d) (vintage_ms V M μ d) ).2.1
lemma preserves (d:ℕ) : t d 0=pureBank Y d:= by rw [ pattern,pred_zero,reports0,vintage_ms, market_zero ]
lemma regular (d:ℕ): (D d).patch (𝒮 d 0):= vintage_ms V M μ d ▸ lucid ( D d ) -- direction check
include he hq
lemma started (d:ℕ): Wait F (fun k=> τ k d) (𝒮 d):= fun i p=> agrees V P M H HI he q hq i μ p.f p.p
lemma realized (d:ℕ) : Wait F (fun k=>s k d) ( t d ):= by
    obtain ht:= started V P M H HI he q hq μ d; exact planner ht (terms (D d) _ ht (regular ..))
-- cancellation identity. keep special parentheses for local notation capture.
theorem trade (d:ℕ) : ∀ᶠ i in F,
       ren (𝔽 i) ((BoxOffice.warehouse V).ftReport hg q i d)=luxury ( Δ i d ) (W i d) ∧ ren (𝔽 i) ( x i d )=s i d:= by
    obtain h0 := rent_calm V P M H HI he d q hq μ; have hT:= started V P M H HI he q hq μ d; have hV (p:Section Y d) : Tendsto (fun i=>ℓ p (ren (𝔽 i) (Λ i d) 0)) F (𝓝 ( ℓ p (pureBank Y d))):=(by simp_rw [renamed ]; exact bank_white _ q hq _ ); have hm (p:Section Y d) : Tendsto (fun i=>ℓ p (τ i d 0)) F (𝓝 ( ℓ p (pureBank Y d))):= (by rw [ ← vintage_ms V M μ d ]; exact hT 0 p );
    obtain hR:= strand (D d) (u:=fun i=>ren (𝔽 i) (Λ i d)) (w:=fun i=> Δ i d) (v:=fun i=> τ i d) ( Eventually.of_forall fun i=> (φconomic ..).symm ) h0 hV hm; filter_upwards [ hR, (D d).patches ( q:=fun i=>Λ i d 0 ) (bank_white (ℙ) q hq) ] with i hi ht; have hm:= warped ( D d ) (Λ i d) (φzero P q μ i) ht; rw [hm] at hi; refine ⟨hi.1,?_⟩;
    change ren (𝔽 i) (predMarket ( (D d).report (Λ i d)) (Λ i d))=_; rw [← same (D d) (Λ i d) (φzero P q μ i) ht, hm ]; exact hi.2
section coupling
variable {R:ℝ}(T:Booth R V.F)(K:Knocker hg T q hq ( warehouse V ))
-- one variable.χ with $η arbitrary$. f=chi.inverse. component.Flex
open Label
abbrev ξ:= metricT T ( t 6 )
abbrev isell (k:ℕ):= metricT T ( stage hg V P H HI q μ k 6 )
-- renormalized profile array in literal q scheme.
def bright (d:ℕ): Word ( Bank V.F d ):= ren (Jet.inverse ( ξ hg V M μ T )) ( pattern hg V M μ d )
local notation "𝔛"=> ξ hg V M μ T
local notation "χ"=> isell hg V P H HI q μ T
local notation "ℚ"=> Bend.curveF (warehouse V) q hg T
local notation "Ω"=> renormal (warehouse V) q hg T
lemma patchesQ (d:ℕ) (u:Pert.Position.Section V.F d) : Tendsto (fun i=> lookie _ u (τ i d 0)) F (𝓝 (lookie _ u (pureBank Y d)) ) := by rw [← vintage_ms V M μ d ]; exact started V P M H HI he q hq μ d 0 u
lemma meterBound : ∀ᶠ i in F, χ i= ren (𝔽 i) ( ℚ i ) := by filter_upwards [trade hg V P M H HI he q hq μ 6] with i hi; unfold isell curveF; rw [← hi.2,meter_ren T ( 𝔽 i) ( uncut hg V q i 6 ) (φzero P q μ i)]
lemma ℚpricing : TurnsOn F χ 𝔛:= by
    let γ₀:= T.normalC; let f i:= s i 6; let v:= t 6; have ht:= realized hg V P M H HI he q hq μ 6;
    let t':= Board7 V.F T.r1; have hu:TurnsOn F (fun i=> t' ∘ f i) (t' ∘ v):= by intro j; refine tendsto_pi_nhds.mpr ?_; intro k; exact (ht j (menu V.F T.r1 k)) -- scope names
    have hw : TurnsOn F (fun i=> Wanted T.r1 ( f i )) ( Wanted T.r1 v ):= present _ hu _ rank_smooth.contDiffAt; intro n; rcases n with _|n; · simp_rw [ show ∀ i, χ i 0=0 from fun _=> metric_zero .., show (ξ hg V M μ T) 0= 0 from metric_zero .. ]; exact tendsto_const_nhds
    have hl (p:Word ( Bank V.F 6 )): metricT T p (n+1)= γ₀⁻¹*(Wanted T.r1 p (n+1)).re:= by simp [metricT,haze, smul_eq_mul,just,γ₀]
    simp_rw [ ξ, isell, hl ]; exact (Complex.reCLM.continuous.continuousAt.tendsto.comp ( hw _ ) ).const_mul _
-- helpers.C.ren. cancellation
include K H HI
lemma χone : 𝔛 1=1:= by
   obtain hv:= ℚpricing hg V P M H HI he q hq μ T 1; apply tendsto_nhds_unique hv ( K.holdsA.congr' ?_ ); filter_upwards [meterBound hg V P M H HI he q hq μ T] with i hi; rw [hi,Jet.tip ( φzero P q μ i ),φone,one_smul]
lemma χlive : Genuine 𝔛:= ⟨ metric_zero .., fun h=> one_ne_zero ( Eq.trans (Eq.symm (χone hg V P M H HI he q hq μ T K)) h ) ⟩
lemma meterLive : (∀ᶠ i in F,Genuine (χ i)) ∧ TurnsOn F (Jet.inverse ∘ χ) (Jet.inverse 𝔛) := inverting ( χlive hg V P M H HI he q hq μ T K ) ( ℚpricing hg V P M H HI he q hq μ T ) ( Eventually.of_forall fun _=> metric_zero ..)
omit he hq K H HI in
private lemma renW {i:Word ℝ}(w:Word ( Bank V.F d ))(v: Section V.F d)(k:ℕ): lookie _ v (ren i w k)= ren i (lookie _ v ∘ w) k:= congr_fun (ren_writes (lookie _ v) _ _) k
lemma turn_meter (d:ℕ): ∀ᶠ i in F,s i d= ren (χ i) (Ω i d):= by
    filter_upwards [ trade hg V P M H HI he q hq μ d, meterBound hg V P M H HI he q hq μ T, K.definedA ] with i hI hk h;
    rw [hk,← hI.2 ]; unfold Bend.renormal Bend.stampT;
    funext n m p; ext1 v; let u:Section V.F d:= ⟨m,v,p⟩; let F':= lookie V.F u; let a:=ℚ i; let U:= F' ∘ x i d;
    have he: (ren ( ren (𝔽 i) a ) ( F' ∘ ren (Jet.inverse a) (x i d)) ) n=ren (𝔽 i) U n:= by rw [ren_writes, ← asc ( φzero P q μ i ) h.1, asc h.1 (lives _),headback h, ren_head ]; -- equality expression annot
    change F' (ren (𝔽 i) (x i d) n)=F' ( ren (ren (𝔽 i) a) (ren (Jet.inverse a) (x i d)) n ); rw [show ∀ a (w:Word (Bank Y d)),F' ( ren a w n )=_ from fun a w=> renW V w u n, show F' _= _ from renW V _ u n ]; exact he.symm
lemma endpoint (d:ℕ): Wait atTop (fun i=> Ω i d) ( bright hg V M μ T d ):= by
   intro n v; obtain ⟨hc,hQ⟩:= meterLive hg V P M H HI he q hq μ T K; let B(i):=s i d;
   obtain hf:= realized hg V P M H HI he q hq μ d; let f:=lookie _ v; have hz:= powersAt (f:= fun i=>f ∘ B i) (fun j=> hf j v) hQ;
   rw [bright,renW ]; refine (hz n).congr' ?_ ; -- defeq ↑function
   filter_upwards [ turn_meter hg V P M H HI he q hq μ T K d,hc ] with i hi hx; change ren ( Jet.inverse (χ i)) (f ∘ s i d) n=_; rw [hi,ren_writes, asc (lives _) hx.1,guarded hx,ren_head ]; rfl
omit he hq K
end coupling
end YM.FVA2.Elegant
