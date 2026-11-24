import YM.OPE.Retained.Niche.Derma
import YM.OPE.Compatible.Moon.Either

/-! The physical OPE estimate on the retained kinetic horizon and transfer. -/
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
variable {g:G.Simple}{s: Sheet G}{p:MapPrices}{H:Votive.Sponsor G}{K:Votive.Seasons H}{a:Axis}{X:Stroke.PriceBook (chart_ok G) K}{t:ℕ→ℕ} {U:Rolls (ThroughLaunch.raise s t)}{P:Spells.Pad G}{D:Desk (ThroughLaunch.raise s t) X a g} {S: Alloy (ThroughLaunch.bountyV s p t) U}
namespace FuelV
variable (C:FuelV g s p H K a X t U P D S)
open OPE.Lake OPE.Allot
variable {l m p' i:ℕ}
variable (u:Ultrafilter (ℕ×ℕ)){F : Extraction.Order}(h:(u:Filter _)≤ F.fuse)
local notation "vν"=> S.B.a.clock.J
noncomputable abbrev constellation (D:Desk (ThroughLaunch.raise s t) X a g)(l:ℕ):= Semester (D.stream l)
local notation "P!"=>constellation D l
local notation "V!"=>ΛBound (S:=S)
local notation "K!"=> C.Holds.label l→L[ℂ] (constellation D l)

-- chronology atom both coordinates grow
lemma July (F:Extraction.Order): Tendsto Prod.snd F.fuse atTop:= Extra.WeakScaling.cofin_snd F
variable (hp:C.refQ l ≤ m)(he:D.cost l ≤ S.B.a.clock.J m)
include hp he h C
def Muse (hp:C.refQ l ≤ m)(he:D.cost l ≤ S.B.a.clock.J m)(q:ℕ×ℕ)(p:K!) :Prop:= ∃ h:m<q.1, ∃ V :C.PlaneQ l m q.1 q.2 hp h, PassportQ C hp h he V ∧ Tplane C hp h he V=p
lemma Plum :∃ f:ℕ × ℕ → C.Holds.label l→L[ℂ] (constellation D l), (∀ᶠ i in u,Muse C hp he i (f i)):= by
       refine Eventually.choice ?_; filter_upwards [(Push.RelayDifference.cutoff_grows F|>.eventually_gt_atTop m).filter_mono h, ((July F).eventually (C.hath hp he)).filter_mono h] with i hi hv; obtain ⟨V,hV⟩:= hv i.1 hi; exact ⟨Tplane C hp hi he V,hi,V,hV,rfl⟩
def Traced (hp:C.refQ l ≤ m)(he:D.cost l ≤ S.B.a.clock.J m)(p:K!):Prop:=∃ f:ℕ×ℕ→ C.Holds.label l →L[ℂ] (constellation D l), (∀ᶠ i in u,Muse C hp he i (f i)) ∧ Tendsto f u (𝓝 p)
lemma obtain_T : ∃ p:K!, Traced C u hp he p:=by
       obtain ⟨f,H⟩:= C.Plum u h hp he; have hp:∀ᶠ i in u,‖f i‖ ≤ ΛBound (S:=S) m:= H.mono (fun i hi=>by obtain ⟨h,V,hV,hT⟩:=hi; exact hT ▸ hV.upl); letI:=FiniteDimensional.proper ℂ (K!); obtain ⟨X,hF⟩:= OPE.Luke.chant u hp; exact ⟨X,f,H,hF⟩
omit h in
lemma Vcap (T:K!)(ht:Traced C u hp he T): ‖T‖ ≤ ΛBound (S:=S) m ∧ ∃ b: (constellation D l)→L[ℂ] C.Holds.label l,T.comp b=ContinuousLinearMap.id .. ∧ ‖b‖≤ ΛBound (S:=S) m:=by
       obtain ⟨p,H,hP⟩:= ht; exact ⟨le_of_tendsto hP.norm (H.mono (fun i hi=> by obtain ⟨h,W,hp,he⟩:=hi; exact he ▸ hp.upl)), OPE.Lake.permitS (J:=fun i=> OPE.Dial.BC (Stroke.dims (D.stream l) i)) u hP (H.mono fun i hi=> by obtain ⟨h,W,hp,he⟩:=hi; exact he ▸ hp.offer)⟩
local notation "μ!"=> Stroke.κBit (D.stream l)
lemma wave (P Q:K!)(A:ℕ→(C.Holds.label l) ≃L[ℂ] (C.Holds.label l)) (hx:Conic C.makes u A)(hP:Traced C u hp he P)(hQ:Traced C u (hp.trans (Nat.le_succ m)) (C.brightC he) Q): Crossing (A m) (A (m+1)) P (E:=fun i=> OPE.Dial.BC (Stroke.dims (D.stream l) i)) Q (μ!:ℝ) m (V! m) (εA (S:=S) m):=by
       obtain ⟨f,Hf,hf⟩:= hP; obtain ⟨g,Hg,hg⟩:= hQ; let T:= arT C.makes l m; have hz:∀ᶠ i in u,‖T i‖≤ΛBound (S:=S) m:= Hf.mono fun i hi=>by
            obtain ⟨hn,W,_⟩:=hi; unfold T arT; rw[dif_pos ⟨hp,hn⟩]; exact steep C hp he hn -- j explicit? check
       let J':= F.fuse; have hT:= arcfocus C.makes (i:=m) u h hx hp hz; refine ⟨OPE.Lake.arriveS u hf hg hT (?_),le_of_tendsto hT.norm hz⟩
       filter_upwards [Hf,Hg,(Push.RelayDifference.cutoff_grows F|>.eventually_gt_atTop (m+1)).filter_mono h, ((July F).eventually (C.boot hp he)).filter_mono h] with i hF hG hv hu; obtain ⟨hk,W,hW,hwp⟩:= hF; obtain ⟨hy,W',hV,hvc⟩:= hG; obtain ⟨X,h,hx⟩:= (hu i.1 hv W W' hW hV).touch; have ht := S.B.a.fits.mono (Nat.le_succ m); have hs:CardinalQ.ages (slender (C.Holds.path.levels.clock.J (m+1))) (OPE.Allot.β C.Holds m) ≤ΛBound (S:=S) m:=Real.exp_monotone (mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (show (S.B.a.clock.J m:ℝ)+1≤_ from add_le_add_left (by exact_mod_cast ht) _)) (show 0 ≤ hill C.Holds m from (hill_pos C.Holds m).le))
       refine ⟨X, ⟨h.toC,h.ofC,h.grace,h.value,h.charge.trans hs,h.inverse.trans hs⟩,?_⟩; rw [←hwp,←hvc]; unfold arT; rw [dif_pos ⟨hp,hk⟩]; exact hx
end FuelV
end YM.PhysicalNext.Repeat.Legato

