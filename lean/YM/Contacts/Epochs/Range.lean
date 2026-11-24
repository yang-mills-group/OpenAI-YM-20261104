import YM.Contacts.Epochs.Timber
import YM.Contacts.Epochs.Casa

/-! # Arbitrary-law scheduling with post-programming access.
 Quantifiers deliberately mirror Trading & Ruese. Supports compound asks on a proof‐relevant Factor,
 allowing time-purchases and Mark/Phase registers fixed without choosing exploration flows;
 `prep` is *method of charging*, not presumed finally. -/
noncomputable section
set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Concert ThroughLaunch Pressure Testing Contacts.Allium Contacts.Allium.Grant
open Contacts.Bounty.Trophy.Lore Contacts.Bounty.Trophy Contacts.Revest Contacts.Revest.Outlay
open Push.SectorMeasure Terrain ConnectedActivityE6 Blaze Push.Uniform Contacts.Milling -- error
open scoped NNReal
variable {v: Patch}{s:Sheet G}{K:MapPrices}{R:Targets s (ThroughLaunch.bearing s K)}{E:Expenses R}
     {z:Return.Wages}
namespace Concert
variable {k l x i j m:ℕ} {β:ℝ}{L:Side}
variable {μ:ℕ→ℕ}{X:ℕ→ℝ} {u:Rolls (ThroughLaunch.raise s μ)} {w:Return.Wages}(W:Register u E w X){V:G.ColorIndex}{F:ℕ→ℕ→Postage}(S:Scouts (F:=F))(p:ℕ→ℕ→JointLoad.Heir.Record)(C:Programs s)
-- anticipation at pre-width. k clocks ≤J
abbrev wish (R:Targets s K) (v:Return.Wages)(f:ℕ→ℕ):= ∀ j i k :ℕ, i ≤ j → k≤j →∀ L:Side,f j≤ L.val→ Concert.before s K R v j i k L
lemma brooms (R:Targets s K)(v:Return.Wages): ∃ f:ℕ→ℕ, wish R v f:= by
    choose f hf using fun i j=> pricing G (s.profile i) (v j i); let H (j:ℕ):= Finset.Iic j; let g j:= (H j).sup (fun i=> max (f i j) ((H j).sup fun k=> Terrain.jetty (R j i) (fabric k))); refine ⟨g,fun j i k hp hq L hh=>?_⟩; have hx : max (f i j) ((H j).sup fun k=> Terrain.jetty (R j i) (fabric k)) ≤ L.val:= le_trans (b:=g j) (Finset.le_sup (f:=fun i=>max (f i j) ((H j).sup fun k=> Terrain.jetty (R j i) (fabric k))) (Finset.mem_Iic.mpr hp)) hh -- expected unknown
    exact ⟨hf _ _ _ ((le_max_left ..).trans hx),(Finset.le_sup (f:=fun k=>Terrain.jetty (R j i) (fabric k)) (Finset.mem_Iic.mpr hq)).trans ((le_max_right ..).trans hx)⟩
local notation "O" => (ThroughLaunch.bearing s K)
local notation "I" => (p j i)
local notation "V₀" => (s.profile i)
local notation "U'" => (s.profile j)
variable {θ:Protection u}
-- fix binder malformed
variable (V:G.ColorIndex) (z:Return.Wages)
structure West (T:Delays θ):Prop where
   porch j i k (hi: StepStages j i)(hk:s.first ≤ i)(hl:k≤j): ∀ x, T.betaEntry j ≤ x→ Fort z W S p C V x k j i
   brim i j k (hi:i ≤ j) (hk:k ≤ j): Trio.maxFixed (dim (R j i|>.halo) (fabric k)) ≤ T.shells j
variable (hg:G.Simple) (hp:EpochSeal s (ThroughLaunch.bearing s K) R E)(hM:wish R z (ThroughLaunch.raise s μ).floorL) (hθ:∀ i j, StepStages j i→ s.first≤ i→ (p j i).ε≤1/4) (U:Delays θ)
include hM hθ hg hp U
lemma westward : ∃ V':Delays θ,DelayLe U V' ∧ ∀ Y:Delays θ,DelayLe V' Y→ West W S p C V z Y:= by
    let P (j:ℕ):= Finset.Iic j; let Q i':=(P i').sup fun i=> (P i').sup fun k=> Trio.maxFixed (dim (R i' i|>.halo) (fabric k)); have ht (j:ℕ)(i:ℕ)(hk:StepStages j i): ∀ᶠ x in atTop, s.first≤ i→ ∀ k∈ P j,Fort z W S p C V x k j i:= by
       by_cases h:s.first≤ i; swap; · simp [h]
       refine ((eventually_all_finset (P j) (p:=fun k x=> Fort z W S p C V x k j i)).mpr (fun k (hp':k∈P j)=> wages z W S p C V hg hp hk (hθ i j hk h) (hM _ _ k hk.1 (Finset.mem_Iic.mp hp') _ (u.large j).need))).mono fun i hi _=> hi
    obtain ⟨T,-,hT,h⟩:= collect_upper U.betaEntry _ (fun j=> eventually_transitions j _ _ (ht j)); refine ⟨{U with betaEntry:=T, shells:= fun i=>max (U.shells i) (Q i)}, ⟨hT,le_rfl,fun _=>le_max_left ..,le_rfl⟩,fun T' hh=> ⟨fun j i k hi hk hl x hx=>h j x ((hh.beta j).trans hx) i hi hk k (Finset.mem_Iic.mpr hl),fun i j k h h'=> le_trans (le_trans (b:=Q j) ((Finset.le_sup (f:=fun k=> Trio.maxFixed (dim (R j i|>.halo) (fabric k))) (Finset.mem_Iic.mpr h')).trans (Finset.le_sup (f:=fun i=>(P j).sup fun k => Trio.maxFixed (dim (R j i|>.halo) (fabric k))) (Finset.mem_Iic.mpr h))) (le_max_right ..)) (hh.shells j)⟩⟩ -- orientation args West ?
end Concert
end YM.PhysicalNext.Repeat.Legato
