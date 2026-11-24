import YM.OPE.Compatible.Moon.Arch
import YM.OPE.Compatible.Eyrie.Meter
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
open Eyrie Extraction -- open for Bid.

variable (B:Table C.Holds.book)(F:Extraction.Order)
local notation "Q"=> C.Holds
-- one-filtration opacity. Uniform in fixed entries up to 2. tolerance can be tiny in p, ascent of support bought along levels.
structure Opacity (C:Fuel g s p H K a X t U P D S) (ε:ℝ) :Prop where
       price : 0<ε
       toll : ε≤1/50
       charge :∀ l r:ℕ,∀ᶠ m:ℕ in atTop,∀ (hp:C.refQ l ≤ m)(he:D.cost l ≤ S.B.a.clock.J m),∃ v:ℕ→ℝ,(∀ i,0<v i) ∧ ∀ᶠ i:ℕ in atTop,∀ N,∀ ht:m+1<N,∀ (R:C.PlaneQ l m N i hp (Nat.lt_trans (Nat.lt_succ_self m) ht)),PassportQ C hp (Nat.lt_trans (Nat.lt_succ_self m) ht) he R→∀ x:C.Holds.label l, ‖x‖ ≤ 2→Pennant (C.Holds.path.rep N i m) (fleet C.Holds.path m r) (v i) ((Owl.Stepm C.makes (d:=l) hp ((Nat.lt_trans (Nat.lt_succ_self m) ht).le) i x).density 0 (C.Holds.localSection l) (C.Holds.path.rep N i m)) → ‖Tplane C hp (Nat.lt_trans (Nat.lt_succ_self m) ht) he R x‖≤ ωCut S m ε
variable {L:Table C.Holds.book}{E:ℕ→Table C.Holds.book}{F':Bin L}{E':DiffPlan B}{tr:Presentation C.Holds}{Z: ∀ d,ℕ→ CoordMap C.Holds d}
lemma fresco (hH: Next.Extract.Base C.Holds F L E F' B E') (ht:Projected tr F F' Z){ε:ℝ}(H:Opacity C ε) (hB:∀ l, RigE.StrongBin C.Holds F' F l): Buoy C B F:=by
        intro l; obtain ⟨r,b,hπ⟩:=(hB l).mark; refine ⟨ε,H.price,H.toll,?_⟩; filter_upwards [H.charge l r] with k h; intro hk hc X hX U hU R hM x he
        have hf := ht.approaches l; let A:=(F' l).step; let T':=(F' l).trueP
        have hμ (x:(Q).label l) (he:B.project l (R.symm x)=0)(hV':‖x‖=1) : ‖U x‖≤ ωCut S k ε:=by
            have hl : (T') (R.symm x)=0:=by
                 have hp: R.symm x∈B.null l := (Submodule.Quotient.mk_eq_zero _).1 he; rw[hH.null l] at hp; exact hp
            obtain ⟨v,hG,hA⟩:=h hk hc; let Y := fun i:ℕ×ℕ=>R.symm x-A i (R.symm x); have hy:Tendsto Y F.fuse (𝓝 (R.symm x)):=by
                 have hp:= (tendsto_const_nhds (x:=R.symm x)).sub (OPE.Luke.arcing hf (R.symm x)); change T' _=0 at hl; rw [show (F' l).trueP _=0 from hl,sub_zero] at hp; exact hp
            have he : Bid.tight C.Holds F Y:=⟨‖R.symm x‖+1, F.fused _ |>.1 (hy.norm.eventually (ge_mem_nhds (by linarith:‖R.symm x‖< ‖R.symm x‖+1)))⟩
            obtain ⟨y,hZ,h_c⟩:=hπ Y (fun i=> by simp only [Y,map_sub,A];
                                                      rw [(F' l).projection]; exact sub_self _) (Work.D01.answer _ C.makes _ _ _ he); obtain ⟨A',ha,hp⟩:=hU
            let fζ (i:ℕ×ℕ):=tallyman C.makes l k i (Y i); have hv: Tendsto fζ X (𝓝 x):= by
                 have hp:= Dash.arcing hM (hy.mono_left hX); rw [show R.toContinuousLinearMap _=x from R.apply_symm_apply _] at hp; exact hp
            apply le_of_tendsto (Dash.arcing hp hv).norm; filter_upwards [(Push.RelayDifference.cutoff_grows F|>.eventually_gt_atTop (k+1)).filter_mono hX, ((July F).eventually hA).filter_mono hX, (Eyrie.compass C.makes y Y hZ h_c hk v hG).filter_mono hX, ha, hv.norm.eventually (ge_mem_nhds (by rw [hV']; norm_num : ‖x‖ < (2:ℝ)))] with i hi hh ht he h_x
            obtain ⟨hM,h',hv,hQ⟩:= he; exact hQ ▸ hh i.1 hi h' hv _ h_x (ht (Nat.le_of_lt hM)) -- cast
        by_cases h:x=0; subst x; rw [map_zero,norm_zero,norm_zero,mul_zero]
        let n:ℂ:=(‖x‖:ℝ); have hv:0<‖x‖:= norm_pos_iff.mpr h; have hc:‖n‖=‖x‖:= (Complex.norm_real ..).trans (Real.norm_of_nonneg hv.le); have hb:= hμ (n⁻¹ • x) (by simp [he]) (by rw [norm_smul,norm_inv,hc,inv_mul_cancel₀ hv.ne']); rw [map_smul,norm_smul,norm_inv,hc,inv_mul_eq_div] at hb; exact (div_le_iff₀ hv).1 hb
end Fuel
end YM.PhysicalNext.Repeat.Legato
