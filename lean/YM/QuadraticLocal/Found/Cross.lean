import YM.QuadraticLocal.Found.Pass
import YM.FullVolume.Cross
/-!
# One qlocal unmarked runway with full local marked walking readiness

(extends proofs of `FullVolume/{Unlatch,Trident,Forge,Cross}`).
Use manually to specialize `WayStation`. Independent of coupling trajectory demands. Bar/Wait
funded receipts for any Ramp when first purchase. Inherited orders leverage and universal estimate
for ALL histories of actual unmarked transition, not asserting `Ramp` pressure.Mark.Q.Ex.Post.
Consumer epoch from `Run.allOrderCred`. Strong K hit fuel stores units before marker.
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
variable (hG:G.Simple){K:KernelChoices}(hK :∀ p : Patch,p.Branches K G){v:Orders}(hp:ThroughLaunch.Draft v)(Q:ℕ→ℕ) (hQ:Monotone Q)(hQ':∀ i,1 ≤ Q i)
include hp hQ hQ' hK hG
theorem rampant_R (he:∀ i,100 ≤ v.supportExp i): ∃ (s:Sheet G)(T:MapPrices)(Y:ℕ→ℝ)(K':Bid.Worth), s.kernel=K ∧ WithStage s v ∧ ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= ThroughLaunch.currency s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),(X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J' ∧ WayStation X)∧∃ (b:Bandage X Y K'), Unlatched b Q (fun _ _ _ _=> True) := by
    obtain ⟨V,W,hV⟩:= Push.Mark.commissioned G (hol G) (Labels.frames G)
    obtain ⟨s,T,C,K',hP,hv,hC⟩ := ruese_R hG hK v hp Q
    let u:Tariffs:=⟨fun _=>0,fun _=>le_rfl,fun _=>1⟩
    let X:Extra.Multi.Scope:=⟨fun _=>1,fun _=>0,fun _=>1,fun _=>le_rfl,fun _=>Nat.zero_lt_one⟩
    obtain ⟨t,hT,hx⟩:= hC u X; obtain ⟨Kc,L,hL⟩:= oyster s W V hV
    have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hv.jets]; exact (le_max_right ..).trans (hp.k i)) tendsto_id
    obtain ⟨z,p,μ,-,-,hμ,hf⟩:= capitalSnow s (ThroughLaunch.bearing s T) ho
    obtain ⟨A⟩:= Next.Rank.exists_budget G
    refine ⟨s,T,C,K',hP,hv,t⊔ L⊔μ,hT.trans (le_sup_left.trans le_sup_left),fun k ht=>?_⟩
    intro M; obtain ⟨hK,hB⟩:= sup_le_iff.mp ht; obtain ⟨hK,hl⟩:=sup_le_iff.mp hK
    obtain ⟨hi,hk⟩:= hx k hK
    let ξ:Extra.Multi.Tariff:= ⟨1,0,fun _=>le_rfl⟩
    refine ⟨hi,fun P=>?_⟩; obtain ⟨w,hk⟩:= hk P; refine ⟨w,fun w' hw Qt E=>?_⟩
    obtain ⟨F,hk⟩:=hk w' hw Qt E ξ; refine ⟨F,fun θ₀ hθ=>?_⟩; obtain ⟨θ,hθ,hk⟩:= hk _ hθ
    refine ⟨θ,hθ,fun Ht J V0=>?_⟩
    let S:Delays θ:= {V0 with shells:= fun i => max (V0.shells i) (snows P i)}
    obtain ⟨a,hα,hδ⟩:= shower Kc S
    obtain ⟨l,h₁,h₂⟩:= hiss Q a; obtain ⟨q,hφ,hM,h₃⟩:= hk Ht J l
    refine ⟨q, (show DelayLe V0 S from ⟨le_rfl,le_rfl,fun _=>le_max_left ..,le_rfl⟩).trans (hα.trans (h₁.trans hφ)),fun V' h D W0=>?_⟩
    have hw:= hα.trans (h₁.trans (hφ.trans h))
    have hG'(i):0≤ generator G i := by unfold generator; positivity
    obtain ⟨Q',Z,hZ,h₄⟩:= franchise M.K A (generator G) hG' hG (hf k).1 (hf k).2 (fun i=> (hB i).trans (P.large i).need) hμ W0
    refine ⟨Z,⟨hZ.1,hZ.2.2,hZ.2.1⟩,fun U ha hb hc aX hz hD=>?_⟩
    obtain ⟨T,B,hF,hA,R,hR,hR₂,hR₃,hR₄,hR₅,⟨b⟩,hp,hπ,H₈,hEst,f,h₅⟩:=h₃ V' h D U aX hz hD
    refine ⟨T,B,hF,R,⟨hR,hR₂,hR₃,hR₄,hR₅,hEst⟩,b,?_⟩
    intro Y hy t ht' F' D₁ Z' hx0 hd ht
    let S:=Family.mk (Issue.trail Y) (hol G) (Labels.frames G) (localSection G) t F'
    have hi:= h₂ V' (hφ.trans h)
    have hm:= hF.symm ▸ hA
    have huv:Mix.paidL S:= hm.factorial
    have hp' :∀ i, 100 ≤ (B.a.budget i).supportExponent:=by
       intro i; change _ ≤ (B.a.params i).supportExponent; rw [params_eq B.valid]; change _ ≤ (s.profile (B.a.clock.J i)).supportExponent; rw [hv.prices]; exact he _
    obtain ⟨hx',hfr,P',A',hhe⟩:= hearthstone Q b Y t hi hQ hQ' hp hp' hG ht' hy hd ht Kc L V W hV (hδ V' (h₁.trans (hφ.trans h))) hL hl hx0
    have hS:=hhe.foundation
    have htX : Extraction.Wcmain S:= gardena S (by exact hm.tabs) hx0 hx'.1 hx'.2 hG huv
    obtain ⟨B',HH,hH⟩:= castle R Y h₅ (C:=S) rfl (fun i=> (le_max_right ..).trans (hw.shells i))
    have hX : Chateau b Q Y t F' D₁:= ⟨ht',hy,hp,hi, hd,ht,⟨M.p,P,θ,V',D,U,M.O,M.K,F,B,Y.history,Y.sticks,rfl,Y.moves⟩,hx0,huv,hx',htX, B',HH,hH,W,P',A',hS, fun g=>rated (B:=B') hx0 hS hG htX g hx' Q' hG' M.O (h₄ S (retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid) B' hH)⟩
    exact ⟨hX,hm.tabs,exodus hG b Y Q t F' D₁ hX hp' H₈ hπ,hfr,⟨V,W,P',A',hV,hhe⟩,warrant (B:=B') hx0 hG hx' Q' hG' M.O (h₄ S (retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid) B' hH),⟨Kc,L,V,W,hδ V' (h₁.trans (hφ.trans h)),hV,hL,hl⟩,trivial⟩

open YM.MergeProof.East
theorem trident_R (he:∀ i,100 ≤ v.supportExp i): ∃ (s:Sheet G)(T:MapPrices)(Y:ℕ→ℝ)(K':Bid.Worth), s.kernel=K ∧ WithStage s v ∧ ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= ThroughLaunch.currency s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),(X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J' ∧ WayStation X)∧∃ (b:Bandage X Y K'), Unlatched b Q (fun T t S _ => let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∀ f:Extraction.Order, CompleteWeak Z f) := by
    obtain ⟨s,T,Y,K',hs,hv,τ,hτ,hA⟩:= rampant_R hG hK hp Q hQ hQ' he
    have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hv.jets]; exact (le_max_right ..).trans (hp.k i)) tendsto_id
    obtain ⟨u,hU⟩:= posters s (ThroughLaunch.bearing s T) ho
    obtain ⟨O⟩:= Next.Rank.exists_budget G
    refine ⟨s,T,Y,K',hs,hv, τ ⊔ u,hτ.trans le_sup_left,fun k hk =>?_⟩
    obtain ⟨hk,hL⟩:= sup_le_iff.mp hk; obtain ⟨hN,hK⟩:= hA k hk; intro M
    have hz : RelayP M.p M.K u:=by
       obtain ⟨b,F,ψ,he,v⟩:= hU.buys
       refine ⟨b,F,ψ,he,v.same,?_,?_,?_⟩
       · intro i; refine ⟨(v.buys i).1,(v.buys i).2⟩
       · intro i; exact ⟨(v.shops i).1⟩
       intro i d j;exact v.lifts i d j
    refine ⟨hN,fun P=> ?_⟩; obtain ⟨U,H⟩:= hK P
    refine ⟨U,fun w hw Q₀ e=>?_⟩; obtain ⟨F,hF⟩:= H w hw Q₀ e
    refine ⟨F,fun u0 hv=>?_⟩; obtain ⟨θ,hθ,hB⟩:= hF u0 hv
    refine ⟨θ,hθ,fun Ht J T0=>?_⟩; obtain ⟨V,hV,hW⟩:= hB Ht J T0
    refine ⟨V,hV,fun V' hv D W=>?_⟩; obtain ⟨Z,hZ,hW⟩:= hW V' hv D W
    obtain ⟨J',hd,hL,hK,H⟩:= sponsored hG M.K O (Next.Foundations.chart G) (Next.Foundations.chart_ok G) _ hz (fun i=>(hL i).trans (P.large i).need) Z
    refine ⟨J',⟨hZ.1.trans hL,hZ.2.1.trans hd,hZ.2.2.trans hK⟩,fun W ha hb hc a h hi=>?_⟩
    obtain ⟨T',B,hF,R,hR,b,hU⟩:= hW W (hL.trans ha) (hK.trans hb) (hd.trans hc) a h hi
    refine ⟨T',B,hF,R,hR,b,?_⟩; intro T t U u Xf G C hxB hp hg
    obtain ⟨hX,hq,hπ,hv,hS,hn,hL',-⟩ := hU T t U u Xf G hxB hp hg; refine ⟨hX,hq,hπ,hv,hS,hn,hL',?_⟩
    obtain ⟨hC,hM,hA,hS,hL₀,S',hA,hC,h₃⟩:= hX.reception
    have hp:= Next.Rank.East.enclosing Xf hX.freight hM
    exact H C (retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid) S' hC hM hp _ _ _ _ _ _ G hS

omit hp hQ hQ' hK
theorem dagger_R {β:ℝ} (h:0<β) : ∃ (M:Metals G)(P:Rolls M.p)(A:Alloy M P)(X:Factor A)(Y:ℕ→ℝ)(K:Bid.Worth)(b:Bandage X Y K),
    A.B.a.clock.kernel.penalty=β ∧ WayStation X ∧ Unlatched b (fun _=>1) (fun T t S _ => let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∀ f:Extraction.Order, MergeProof.East.CompleteWeak Z f) := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G β h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= trident_R hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let M:=ThroughLaunch.currency s T l
  obtain ⟨⟨P⟩,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,hU⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  exact ⟨_,_,_,_,_,_,c,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,W.2.2.2.2.2,hU⟩


open FullVolume
omit hG

theorem Run.attain (h : G.Simple) (b : ℝ) (hp : 0<b) : ∃ R : Run G, R.family.path.levels.clock.kernel.penalty=b ∧ WayStation R.kit:=by
   obtain ⟨M,P,A,X,Y,K,bC,hK,hξ,h⟩:= dagger_R h hp
   obtain ⟨T,⟨Z⟩⟩:= rod (by assumption) X
   choose t ht using fun d:ℕ=> (A.B.a.fits.deep.eventually_ge_atTop (d+3)).exists
   obtain ⟨D,S,hm,hc,hH,hF⟩:= squad (by assumption) bC T Z.receipts t ht
   exact ⟨⟨_,_,_,_,_,_,bC,_,h,T,Z,t,ht,D,S,hm,hH,hF⟩,hK,hξ⟩


end YM.PhysicalNext.Repeat.Legato
