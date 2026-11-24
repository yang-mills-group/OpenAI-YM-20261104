import YM.FVA2.PayAll
/-!
# Actual normalization on point supplier and cancellation even under continuous-center support.

No estimates carried through the ill-conditioned preperiodic operators.
-/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.FVA2.Elegant
open Function Filter Set MeasureTheory PositionX
open Pert Pert.Position Maxwell Maxwell.Free PositionX.Bare.Shop PositionX.Jet
open PositionX.Ribbon PositionX.Detector PositionX.Bend
open Lattice Topology Elegant
open MS MS.Menus MS.Land MS.Theater MS.Book MS.Book.Program MS.Book.Convolve MS.Orbit MS.Tide MS.Rake
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend BoxOffice Blaze Frost ArchTurn
open PowerSeries WorldJet Counterpart
open Fountain PayAll
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(hg:G.Simple){B:Booked (wings G)} (V:Warehouse G)(P: Prescription (wings G))(M:MS_Data G B)
variable (H:ExactSpin V P)(HI:Trusted P)(he: MixedStory.AllProfiles M V P) (q:ℕ+)(hq:1<q.val)(μ:ℝ) {d n:ℕ}
local notation "Y"=> V.F
local notation "ℙ"=> BoxOffice.warehouse V
local notation "δ"=> nested V.F hg (BoxOffice.warehouse V)
local notation "𝒮"=> Spring.ms V M μ
local notation "F"=> (atTop:Filter ℕ)
local notation "W"=> Bank V.F d
local notation "E₀"=> E V.F d
local notation "Ξ"=> (𝒮 d)
local notation "Pp" d=> turns hg V M μ d
-- position extraction includes this normalization before coupling inversion
lemma exactD (d:ℕ) : (δ d).announce (𝒮 d) (Pp d) := by -- D undefined
    exact ( solves_only (nested V.F hg ( warehouse V ) d) (𝒮 d) (Spring.vintage_ms ..) ).1
lemma family (h:n≤d) : zoomL Y h ∘ (turns hg V M μ d)=turns hg V M μ n := by
    let u:= zoomL Y h; let D' := nested V.F hg (warehouse V) d; let A (d):= turns hg V M μ d; obtain H:= solves_only (nested V.F hg (warehouse V) n) (𝒮 n) (Spring.vintage_ms ..); refine H.2.2 _ ?_ ?_; rw [Function.comp_apply, Elegant.reports0,map_zero]
    have hm: (pulls (up Y h)) ∘ 𝒮 d= 𝒮 n:= funext fun i=> Spring.valley_ms ..; unfold announce; rw [ ← hm, pred_pulls ]; funext i; have hp:= congr_fun (show D'.D ∘ predMarket ( A d ) (𝒮 d)=Jet.just ( (D').D (pureBank V.F d)) from exactD hg V M μ d ) i; rw [Function.comp_apply] at hp; rw [Function.comp_apply,Function.comp_apply,←zoom_compat V.F hg (warehouse V) h, hp]; unfold just; split; rw [zoom_compat, pure_zoom ]; rw [map_zero ]
-- payroll finite coordinates X scheme points. currency = g_* at bare. graph θ on metric.
section m
local notation "MM"=> MS.Dial.tour -- unused
open PertExtension.LatticePT (side epsilon origins Grid.sample) -- syntax
local notation "N₀" s=> Site (side q s)
variable (m:ℕ)
abbrev unregX (p: Lattice.Site (side q m))(u:Fin n → Lattice.Site (side q m)) (d i:ℕ): PayAll.hall V.F d n:= (PowerSeries.coeff (R:=ℂ) i).compMultilinearMap ( Counterpart.rawL V q m u p d ) -- k remove
abbrev phy (x:Points n)(d:ℕ): Word (PayAll.hall V.F d n):= fun i=> Fountain.phys V M μ i x d
def sounded (p:Lattice.Site (side q m))(u:Fin n→Lattice.Site (side q m))(d i:ℕ) := ( coeff (R:=ℂ) i|>.compMultilinearMap ( tuition V P H HI q m μ p u d ) )
local notation "Wμ" m=> bust hg V P H HI q μ m
local notation "𝔽"=> clockM P q μ
abbrev feeUp (p:Lattice.Site (side q m))(u:Fin n→ Lattice.Site (side q m))(d: ℕ) := heated (unregX V q m p u d) ((BoxOffice.warehouse V).ftReport hg q m d) -- binder wrong
abbrev projected (p:Lattice.Site (side q m))(u:Fin n→ Lattice.Site (side q m))(d: ℕ):= heated (sounded V P H HI q μ m p u d) ( bust hg V P H HI q μ m d )
variable {c:ℝ}(T:Booth c V.F)(Z:Knocker hg T q hq (warehouse V))
def counter (p:Lattice.Site (side q m))(u:Fin n→ Lattice.Site (side q m))(d:ℕ) : Word (PayAll.hall V.F d n):= ren (stampT (ℙ) q hg T m) ( feeUp hg V q m p u d )
abbrev cost (x:Points n)(d:ℕ):= heated (phy V M μ x d) (turns hg V M μ d)
def trueK (x:Points n)(d:ℕ):= ren ( Jet.inverse (Elegant.ξ hg V M μ T) ) (cost hg V M μ x d)
local notation "Σq"=> curveF ℙ q hg T
local notation "Σξ"=> isell hg V P H HI q μ T
local notation "Ω"=> dawnFrame V P H HI q μ
local notation "𝒟"=> Elegant.ξ hg V M μ T
local notation "Tx"=> Test n
variable (p:Lattice.Site (side q m))(u:Fin n→ Lattice.Site (side q m))
lemma work (d:ℕ): heated ( ren (𝔽 m) (unregX V q m p u d)) (Ω m d)= sounded V P H HI q μ m p u d:= by
    let W₀:=Counterpart.rawL V q m u p d; let R:= stencil ( shift P.team (μ-Pond.clock q m) ); let A:= unregX V q m p u d;
    have hx(i:ℕ): ren (𝔽 m) A i= (coeff (R:=ℂ) i).compMultilinearMap ( R.compMultilinearMap W₀ ):= by
       ext1 v; let T:= PayAll.value («F»:=Y) v; have he:T ∘ A=Clock.out ( W₀ v ):= rfl;
       change (T ∘ ren (𝔽 m) A) i= Clock.out (R (W₀ v)) i; rw [ ren_writes, he ]; exact (congr_fun (WorldJet.ren_clock P.team (μ-Pond.clock q m) (W₀ v)) _).symm
    funext i; ext1 v; exact (PayAll.slit (ren (𝔽 m) A) (Ω m d) _ v hx i).symm
include Z he H HI hq
lemma movement (d:ℕ): ∀ᶠ i in atTop, ∀ m' (p:Lattice.Site (side q i)) (u:Fin m'→ Lattice.Site (side q i)),
       ren (𝔽 i) (feeUp hg V q i p u d)=projected hg V P H HI q μ i p u d ∧
       projected hg V P H HI q μ i p u d= ren ( Σξ i ) (counter hg V q i T p u d):= by
    filter_upwards [ trade hg V P M H HI he q hq μ d, meterBound hg V P M H HI he q hq μ T, Z.definedA ] with i h hp hi n p u; let FI:= unregX V q i p u d;
    have hx: ren (𝔽 i) ( feeUp hg V q i p u d )=projected hg V P H HI q μ i p u d:= by unfold feeUp projected; rw [PayAll.gathers _ _ _ (φzero P q μ i), h.1,← occupies, work ]
    refine ⟨ hx, ?_⟩; rw [← hx, hp, counter ]; funext j; ext1 v; let U:= feeUp hg V q i p u d; let a:=𝔽 i; let f:=PayAll.value v ( «F» := V.F ) (d:=d); let b:= Σq i; change ( f ∘ ren a U ) j=( f ∘ ren (ren a b) ( ren (inverse b) U )) j; rw [ren_writes, ren_writes, ren_writes, ← asc (φzero P q μ i) hi.1, asc hi.1 (lives _),headback hi,ren_head ]
variable (O:(i:ℕ)→ Lattice.Site (side q i)) (U:(i:ℕ)→ Fin n→ Lattice.Site (side q i))
  (hO:∀ᶠ i in atTop,O i∈ origins q i){x:Points n}(hx:x∈conf n)(hU:Tendsto (fun i=> PertExtension.LatticePT.Grid.sample q i (U i)) atTop (𝓝 x))
include hO hU hx
lemma realizes_point (d:ℕ) : Saw atTop (fun i=> counter hg V q i T ( O i ) (U i) d ) ( trueK hg V M μ T x d ):= by
   let X(i):= sounded V P H HI q μ i ( O i ) ( U i ) d; let P' (i:ℕ):= projected hg V P H HI q μ i ( O i ) ( U i ) d;
   have heX:Saw F X (phy V M μ x d):= fun p n=> Fountain.density V P M H HI he q hq μ n p O hO x hx U hU;
   have hc:Saw atTop P' (cost hg V M μ x d):= PayAll.upgrade _ _ heX (terms (δ d) _ ( started V P M H HI he q hq μ d ) (regular ..))
   let σ:= inverse 𝒟;
   obtain ⟨h₃,h₄⟩:= meterLive hg V P M H HI he q hq μ T Z;
   intro p n'; unfold trueK; rw [ value_ren ]; refine ( powersAt ( f:=fun i=> PayAll.taste (P' i) p ) ( p:= inverse ∘ Σξ ) (hc p) h₄ n' ).congr' ?_; filter_upwards [movement hg V P M H HI he q hq μ T Z d,h₃] with i hi ht; obtain h: P' i= ren (Σξ i) ( counter hg V q i T ( O i ) (U i) d ):= ( hi _ _ _ ).2;
   change ren _ (PayAll.taste (P' i) p) _=_; rw [h, value_ren ]; change ren ( Jet.inverse (Σξ i) ) _ _= _; rw [ asc ( lives (Σξ i) ) ht.1, guarded ht, ren_head ];
end m
end YM.FVA2.Elegant
