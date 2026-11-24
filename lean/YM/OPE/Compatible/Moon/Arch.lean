import YM.OPE.Compatible.Moon.Fare
import YM.OPE.Compatible.Village.Emperors
import YM.OPE.Compatible.Moon.Either
import YM.OPE.Compatible.Niche.Nook
import YM.OPE.Compatible.Niche.Whisper
import YM.OPE.Compatible.Niche.Tech
import YM.OPE.Rough.Supply
import YM.OPE.Compatible.Calendars.Repeat
/-!
# Augmented supplies on one construction

Acquire or consume extra quantitative certificates. Here hypotheses/function
inputs still specify which purchases are needed; `FinalBeam` / `Clients.Jacob`
for actually obtaining all the properties needed for the extension on the same
construction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent

variable (hG:G.Simple)
open OPE OPE.Owl
set_option quotPrecheck false
variable {g:G.Simple}{s: Sheet G}{p:MapPrices}{H:Votive.Sponsor G}{K:Votive.Seasons H}{a:Axis}{X:Stroke.PriceBook (chart_ok G) K}{t:ℕ→ℕ} {U:Rolls (ThroughLaunch.raise s t)}{P:Spells.Pad G}{D:Desk (ThroughLaunch.raise s t) X a g} {S: Alloy (ThroughLaunch.currency s p t) U}
namespace Fuel
variable (C:Fuel g s p H K a X t U P D S)
open OPE.Lake OPE.Allot
variable {l m p' i:ℕ}
variable (u:Ultrafilter (ℕ×ℕ)){F : Extraction.Order}(h:(u:Filter _)≤ F.fuse)
local notation "vν"=> S.B.a.clock.J

local notation "P!"=>constellation D l
local notation "V!"=>ΛBound (S:=S)
local notation "K!"=> C.Holds.label l→L[ℂ] (constellation D l)

variable (ε:ℝ)
noncomputable abbrev ωCut (Z:Alloy (ThroughLaunch.currency s p t) U)(m:ℕ)(ε:ℝ):ℝ:= OPE.CardinalQ.ages (-1-ε) (Z.B.a.clock.hatBeta m)
-- LeakZ remains quantitative, EOM currently upstream.Power. -
variable (T:Table C.Holds.book) {Φ:Extraction.Order}
variable (hp:C.refQ l ≤ m)(he:D.cost l≤ S.B.a.clock.J m)
def Leak (T:Table C.Holds.book)(l m:ℕ)(hp:C.refQ l ≤ m)(he:D.cost l ≤ S.B.a.clock.J m)(ε:ℝ)(F:Extraction.Order):Prop:=∀ (u:Ultrafilter (ℕ×ℕ)), (u:Filter _) ≤ F.fuse→ ∀ P:C.Holds.label l→L[ℂ]constellation D l, Traced C u hp he P→∀ A: C.Holds.label l≃L[ℂ]C.Holds.label l, Tendsto (tallyman C.makes l m) u (𝓝 A.toContinuousLinearMap)→ ∀ x:C.Holds.label l,T.project l (A.symm x)=0→ ‖P x‖ ≤ ωCut S m ε*‖x‖
def Buoy (T:Table C.Holds.book)(F:Extraction.Order):Prop:= ∀ l:ℕ, ∃ ε:ℝ,0<ε∧ε≤1/50∧∀ᶠ m:ℕ in atTop,∀ hp he, Leak C T l m hp he ε F
include h
lemma relay {k:ℕ} (hp :C.refQ l ≤ k)(he:D.cost l ≤S.B.a.clock.J k)(hm:∀ i:ℕ, k≤ i→∀ a b,Leak C T l i a b ε F)(hy:ε ≤1/50):
        ∃ q:ℕ→ C.Holds.label l ≃L[ℂ] C.Holds.label l,Conic C.makes u q ∧ Ferried k (Stroke.κBit (D.stream l)) (ΛBound (S:=S)) (fun i=>ωCut S i ε) l q (fun i=>Dial.BC (Stroke.dims (D.stream l) i)) T:=by
       obtain ⟨Y,H⟩:= Enc C.makes u h l; choose! Z hZ using fun i (hi:k ≤ i)=> C.obtain_T u h (hp.trans hi) (he.trans (S.B.a.fits.mono hi)); refine ⟨Y,H, ⟨Z,?_⟩⟩
       intro i hi
       have hp':= hp.trans hi; have hz:= he.trans (S.B.a.fits.mono hi); have hy': OPE.Stroke.MatchZ.tuneJ ≤ -1-ε:=by unfold OPE.Stroke.MatchZ.tuneJ; linarith
       obtain ⟨hp,hF⟩:= C.Vcap u hp' hz (Z i) (hZ i hi); refine ⟨⟨hp,hF,hm i hi hp' hz u h (Z i) (hZ i hi) (Y i) (H.meeting i hp')⟩,?_⟩
       obtain ⟨⟨x,hx,hq⟩,hc⟩:= C.wave u h hp' hz (Z i) (Z (i+1)) Y H (hZ i hi) (hZ (i+1) (hi.trans (Nat.le_succ i)))
       exact ⟨⟨x,hx,hq.trans (Real.exp_monotone (mul_le_mul_of_nonneg_right hy' (show 0≤ Lake.hill C.Holds i from (hill_pos C.Holds i).le))) ⟩,hc⟩
omit h
lemma ΔHope (F:Extraction.Order)(V:Spec.Final C.Holds F T)(h:Buoy C T F):Concourse C.makes F T:=by
       let R:=C; refine ⟨?_,fun l=>?_ ⟩; · exact Eventually.of_forall (fun m=> (show 16≤ extent C.Holds m by exact_mod_cast C.time m))
       let Z:= D.stream l; let Y:= fun i=> Dial.BC (Stroke.dims Z i); obtain ⟨ε,hε,hb,hh⟩:= h l
       obtain ⟨k,hV⟩:= eventually_atTop.mp (hh.and ((eventually_ge_atTop (C.refQ l)).and (S.B.a.fits.deep.eventually_ge_atTop (D.cost l))))
       obtain ⟨hp,he⟩:= hV k le_rfl|>.2; refine ⟨Y,inferInstance,inferInstance,inferInstance,OPE.Luke.Queen Z V.phase.transport.comparator,k,hp,ε, (Stroke.κBit Z), ΛBound (S:=S), fun i=>ωCut S i ε,hε, Nat.cast_nonneg _, C.Θacts.pays (hill_high g),RateLE.exp (-1-ε) (hill_high (C:=C.Holds) g),fun i _=>Real.exp_nonneg _,fun f hf hl=>?_⟩
       letI:=hf; let u:=Ultrafilter.of f; exact ⟨u,u.neBot,Ultrafilter.of_le f,relay C u ((Ultrafilter.of_le f).trans hl) ε T hp he (fun i hi=> (hV i hi).1) hb⟩ -- nested exists type?
lemma ΦEstimate (F:Extraction.Order)(V:Spec.Final C.Holds F T)(hp:Services C.Holds F T)(h:Buoy C T F): OPE.Arboreal.Trace.CrownLaw V:=by
       obtain ⟨W⟩:= C.rank_prepare.2.2; exact OPE.Arboreal.Trace.attaches V W (Concourse.tender (C.ΔHope T F V h) V.phase.transport.injection hp) hp
end Fuel
end YM.PhysicalNext.Repeat.Legato
