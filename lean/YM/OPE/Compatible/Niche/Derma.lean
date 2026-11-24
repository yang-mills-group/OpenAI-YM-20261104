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
include C
abbrev PlaneQ (l m N p:ℕ)(h: C.refQ l ≤ m)(hv:m<N):= Tail C.amp C.refQ C.shifts C.makes h (p:=p) hv
variable {l m N j:ℕ}{φ:Filter (ℕ×ℕ)} {k₁ k₂:ℝ}
local notation "j₀"=> C.Holds.path.levels.clock.J
noncomputable abbrev Tplane (hp:C.refQ l≤ m)(hv:m<N)(he:D.cost l≤ S.B.a.clock.J m) (Q:C.PlaneQ l m N j hp hv):= Scan C.amp C.refQ C.shifts C.makes C.trek.turtle C.tell g D P he hp hv (p:=j) Q
abbrev PassportQ (hp:C.refQ l≤ m)(hv:m<N)(he:D.cost l≤ S.B.a.clock.J m)(Q:C.PlaneQ l m N j hp hv):= Festival C.amp C.refQ C.shifts C.makes C.trek.turtle C.tell g D P he hp hv (p:=j) Q
noncomputable def ΛBound (m:ℕ):ℝ:= CardinalQ.ages (slender (S.B.a.clock.J m)) (S.B.a.clock.hatBeta m)
noncomputable def εA (m:ℕ):ℝ:= CardinalQ.ages Stroke.MatchZ.tuneJ (S.B.a.clock.hatBeta m)
variable (hp :C.refQ l ≤ m)(he:D.cost l ≤S.B.a.clock.J m)
include hp he
lemma hath : ∀ᶠ j:ℕ in atTop,∀ N:ℕ,∀ hu:m<N, ∃ Q : C.PlaneQ l m N j hp hu, PassportQ C hp hu he Q:= Lands C.amp C.cabinet C.refQ C.shifts C.makes C.trek.turtle C.tell g D P he C.trek.costE hp
abbrev brightC (_C:Fuel g s p H K a X t U P D S)(he:D.cost l ≤ S.B.a.clock.J m) : D.cost l ≤ S.B.a.clock.J (m+1) :=pursuit g D he
lemma boot : ∀ᶠ j:ℕ in atTop,∀ N:ℕ,∀ hu:m+1<N,∀ (Q:C.PlaneQ l m N j hp (Nat.lt_trans (Nat.lt_succ_self _) hu)) (F:C.PlaneQ l (m+1) N j (hp.trans (Nat.le_succ m)) hu), PassportQ C hp (Nat.lt_trans (Nat.lt_succ_self _) hu) he Q → PassportQ C _ hu (brightC C he) F → Owl.Plasma (D.stream l) (Stroke.dims (D.stream l)) (C.Holds.S.block m) (Stroke.κBit (D.stream l)) (Allot.β C.Holds m) (Allot.β C.Holds (m+1)) (slender (S.B.a.clock.J (m+1))) (OarX (p:=j) (m:=m) C.makes (d:=l) hp (Nat.lt_trans (Nat.lt_succ_self m) hu)).toContinuousLinearMap (Tplane C (hp.trans (Nat.le_succ m)) hu (brightC C he) F) (Tplane C hp (Nat.lt_trans (Nat.lt_succ_self _) hu) he Q):= by
       filter_upwards [Concordia C.amp C.cabinet C.refQ C.shifts C.makes C.trek.turtle C.tell g D P he C.trek.costE C.sat C.trek.hold.placed.nest hp] with j h; exact fun i hi Q F ht hk=> h i hi F Q hk ht
lemma steep (hv:m<N): ‖(OarX C.makes (m:=m) (d:=l) hp hv j).toContinuousLinearMap‖≤ΛBound (S:=S) m:=by
       let a:=S.B.a; let J':=a.clock.J; let v:= a.clock.hatBeta m; have hh:= C.trek.analysisK (J' (m+1)) l (le_trans (D.stretch l) (brightC C he)) v (S.B.valid.pays m); let K:= OarX C.makes (m:=m) (d:=l) hp hv j; have ht:= Singer C.makes (d:=l) (p:=j) (m:=m) hp hv; apply ht.trans
       change YieldP ((Labels.frames G).level l) (S.B.a.S.block m) (S.B.a.params (m+1))≤ _; rw [depQ,params_eq S.B.valid]; apply hh.1.trans (Real.exp_monotone ?_); apply mul_le_mul_of_nonneg_right _ (show 0≤ Real.log v from Real.log_nonneg (a.fits.delayed m).le); apply inv_anti₀ (by positivity) (show (S.B.a.clock.J m:ℝ)+1≤_ from add_le_add_left (by exact_mod_cast (a.fits.mono (Nat.le_succ m))) _)
omit hp he
lemma Θacts : RateIs atTop (Lake.hill C.Holds) (ΛBound (S:=S)) 0 :=by
       let T:= C.Holds; let g:=(ΛBound (S:=S)); let h(i:ℕ):=Lake.hill C.Holds i; refine ⟨Eventually.of_forall fun i=> (Real.exp_pos _),?_ ⟩
       have he:Tendsto (fun i=>(j₀ i:ℝ)+1) atTop atTop:= ((tendsto_natCast_atTop_atTop.comp C.Holds.path.levels.fits.deep).atTop_add tendsto_const_nhds)
       refine (tendsto_inv_atTop_zero.comp he).congr fun i=>?_ ; unfold ΛBound CardinalQ.ages; rw [Real.log_exp]; exact (mul_div_cancel_right₀ (slender (S.B.a.clock.J i)) (Lake.hill_pos C.Holds i).ne').symm
end Fuel
end YM.PhysicalNext.Repeat.Legato
