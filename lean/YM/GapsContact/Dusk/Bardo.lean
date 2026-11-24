import YM.GapsContact.Dusk.Expend
import YM.Frontier6.Multi.Bonds.Deep
import YM.TraceExtension.Made.Bardo
/-! Joint (Chateau, canopy, detector costs, Trace Gallery) producer. Variant of
    Feathers and Bardo. -/
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
-- Can use for other payments. order pressure. Extant reading‐Z every point, Tied Stories mongoose.Beta.
variable (hG:G.Simple){K:KernelChoices}(hK :∀ p : Patch,p.Branches K G){v:Orders}(hp:ThroughLaunch.Draft v)(Q:ℕ→ℕ) (hQ:Monotone Q)(hQ':∀ i,1 ≤ Q i)
include hp hQ hQ' hK hG
lemma ballyD (he:∀ i,100 ≤ v.supportExp i): ∃ (s:Sheet G)(T:MapPrices)(Y:ℕ→ℝ)(K':Bid.Worth), s.kernel=K ∧ WithStage s v ∧ ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= ThroughLaunch.currency s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),(X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J')∧∃ (b:Bandage X Y K'), ∃ T t S D,Chateau b Q T t S D ∧ Stock.Tabs B.a ∧ (let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S;
        ColumnSteps Z K' ∧ Fridge Z (far B.a) (fly B.a) ∧ Velour Z (renal B.a) (mutt B.a Q) D ∧ VelourArity Z (renal B.a) (mutt B.a Q) D ∧ Pillows Z (renal B.a) (mutt B.a Q) D ∧ LightArity Z (renal B.a) (mutt B.a Q) D ∧ GapsContact.Dusk.Shipper Z.path (mutt B.a Q) D ∧ Quince.Skill b (Quince.bear K')) := by
    obtain ⟨V,W,hV⟩:= Push.Mark.commissioned G (hol G) (Labels.frames G)
    obtain ⟨s,T,C,K',hP,hv,hC⟩ := rueseD hG hK v hp Q
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
    obtain ⟨T,B,hF,hA,R,hR,hR₂,hR₃,hR₄,hR₅,⟨b,htq⟩,hp,hπ,H₈,H₉,hXD,f,h₅⟩:=h₃ V' h D U aX hz hD
    refine ⟨T,B,hF,R,⟨hR,hR₂,hR₃,hR₄,hR₅⟩,b,?_⟩
    choose t ht using fun d=> (aX.fits.deep.eventually_ge_atTop (d+3)).exists
    have ht':∀ d,d+3 ≤ B.a.clock.J (t d):=by rw [hF]; exact ht
    obtain ⟨Y,hy⟩:=Graces.winnow hG R
    obtain ⟨D₁,F',hx0,hc',hd,hsteps,h_tt⟩:= squadLeading hG b Y hy t ht'
    let S:=Family.mk (Issue.trail Y) (hol G) (Labels.frames G) (localSection G) t F'
    have hi:= h₂ V' (hφ.trans h)
    have hm:= hF.symm ▸ hA
    have huv:Mix.paidL S:= hm.factorial
    have hp' :∀ i, 100 ≤ (B.a.budget i).supportExponent:=by
       intro i; change _ ≤ (B.a.params i).supportExponent; rw [params_eq B.valid]; change _ ≤ (s.profile (B.a.clock.J i)).supportExponent; rw [hv.prices]; exact he _
    obtain ⟨hx',P',A',hS⟩:= chaletrail Q b Y t hi hQ hQ' hp hp' hG ht' hy hd h_tt Kc L V W hV (hδ V' (h₁.trans (hφ.trans h))) hL hl hx0
    have ht : Extraction.Wcmain S:= gardena S (by exact hm.tabs) hx0 hx'.1 hx'.2 hG huv
    obtain ⟨B',HH,hH⟩:= castle R Y h₅ (C:=S) rfl (fun i=> (le_max_right ..).trans (hw.shells i))
    have hX : Chateau b Q Y t F' D₁:= ⟨ht',hy,hp,hi, hd,h_tt, hc',hx0,huv,hx',ht, B',HH,hH,W,P',A',hS, fun g=>rated (B:=B') hx0 hS hG ht g hx' Q' hG' M.O (h₄ S (retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid) B' hH)⟩
    have h_fr : Fridge S (far B.a) (fly B.a) :=
      freezes hG (fun N p=>⟨Planned.GuardedAtom.Guard.Keeper.sufficient (hy.born N p)⟩) (fun i => by
        change step_cost (B.a.params i) ≤ B.a.clock.hatBeta i
        rw [params_eq B.valid]
        exact (hδ V' (h₁.trans (hφ.trans h)) _ _ (step_paid _ i) _ (B.valid.pays i)).1)
    exact ⟨Y,t,F',D₁,hX,hm.tabs, hsteps,h_fr,exodus hG b Y Q t F' D₁ hX hp' H₈ hπ, exodusN hG b Y Q t F' D₁ hX hp' H₈ hπ, exodusAll hG b Y Q t F' D₁ hX hp' H₈ hπ, exodusL hG b Y Q t F' D₁ hX hp' H₈ hπ H₉, traffic hG b Y Q hy hp hXD hp' D₁ (fun N p m hi=> hd N m p hi),htq⟩

end YM.PhysicalNext.Repeat.Legato
end
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
open YM.MergeProof.East

-- Another grantor for buying universal weak supplies. Can still extend before-L clocks, after-L Delays, extra Paid W and layouts. retains
variable (hG:G.Simple){K:KernelChoices}(hK :∀ p : Patch,p.Branches K G){v:Orders}(hp:ThroughLaunch.Draft v)(Q:ℕ→ℕ) (hQ:Monotone Q)(hQ':∀ i,1 ≤ Q i)
include hp hQ hQ' hK hG
lemma meranoD (hQ2:∀ i,2≤ Q i) (he:∀ i,100 ≤ v.supportExp i): ∃ (s:Sheet G)(T:MapPrices)(Y:ℕ→ℝ)(K':Bid.Worth), s.kernel=K ∧ WithStage s v ∧ ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= ThroughLaunch.currency s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),(X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J')∧∃ (b:Bandage X Y K'), ∃ T t S D,Chateau b Q T t S D ∧ Stock.Tabs B.a ∧ (let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S;
        ColumnSteps Z K' ∧ Fridge Z (far B.a) (fly B.a) ∧ Velour Z (renal B.a) (mutt B.a Q) D ∧ VelourArity Z (renal B.a) (mutt B.a Q) D ∧ Pillows Z (renal B.a) (mutt B.a Q) D ∧ LightArity Z (renal B.a) (mutt B.a Q) D ∧ GapsContact.Dusk.Shipper Z.path (mutt B.a Q) D ∧ ∀ f:Extraction.Order, CompleteWeak Z f ∧ Trace.Over.Gallery Z f) := by
    obtain ⟨s,T,Y,K',hs,hv,τ,hτ,hA⟩:= ballyD hG hK hp Q hQ hQ' he
    have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hv.jets]; exact (le_max_right ..).trans (hp.k i)) tendsto_id
    obtain ⟨u,hU⟩:= posters s (ThroughLaunch.bearing s T) ho
    obtain ⟨O⟩:= Next.Rank.exists_budget G
    obtain ⟨uB,hU'⟩:= submits (ThroughLaunch.bearing s T) s ho
    obtain ⟨uW,hUW⟩:= Trace.Perfect.vroom s
    refine ⟨s,T,Y,K',hs,hv, (τ ⊔ u)⊔(uB⊔(uW⊔Trace.Terrace.ctl)),hτ.trans (le_sup_left.trans le_sup_left),fun k hk =>?_⟩
    obtain ⟨hk,ht₀⟩:=sup_le_iff.mp hk; obtain ⟨hi₁,hi₂⟩:=sup_le_iff.mp ht₀; obtain ⟨hw0,hCtl⟩:=sup_le_iff.mp hi₂
    have heSup:=hv
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
    refine ⟨θ,hθ,fun Ht J T0=>?_⟩
    obtain ⟨V₁,h1,hΩ⟩:= Trace.Terrace.staircase (X:=M.p) hCtl T0
    obtain ⟨D0,hd⟩:=hUW k hw0 P
    let T2: Delays θ:= {V₁ with betaEntry:=D0 ⊔ V₁.betaEntry}
    obtain ⟨T3,h2,h3⟩:= Trace.Margin.flows T2 hG; obtain ⟨T4,ht₄,hβ⟩:= Quince.rise_B T3
    obtain ⟨V,hV,hW⟩:= hB Ht J T4
    have hζ:DelayLe V₁ V:= (show DelayLe V₁ T2 from ⟨fun i=>le_max_right ..,le_rfl,le_rfl,le_rfl⟩).trans (h2.trans (ht₄.trans hV));
    have hcT:(D0:ℕ→ℝ)≤V.betaEntry:= fun i=>le_trans (b:=T2.betaEntry i) (le_max_left ..) ((h2.trans (ht₄.trans hV)).beta i)
    refine ⟨V,h1.trans hζ,fun V' hv D W=>?_⟩; obtain ⟨Z,hZ,hW⟩:= hW V' hv D W
    obtain ⟨J',hN₁,hL,hK,H⟩:= sponsored hG M.K O (Next.Foundations.chart G) (Next.Foundations.chart_ok G) _ hz (fun i=>(hL i).trans (P.large i).need) Z
    let z(s):= ∑ i∈Finset.range (s+1), generator G i
    have ht':∀ i j,i ≤ j → generator G i ≤ z j:= fun i j h=> Finset.single_le_sum (fun i _=>by unfold generator; positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le h)); have hz₁(i):0 ≤ z i:=Finset.sum_nonneg (fun i _=> by unfold generator;positivity)
    have hvU:RelaySky M.K uB (X:=M.p):=by
        obtain ⟨a,hM,h,P,V,hN,hB⟩:=hU'.asks; refine ⟨a,hM,h,P,V,⟨hN.later,?_,hN.pin⟩,hB⟩; intro i j hi x; have ht:= hN.costs i j hi x; refine ⟨ht.1,fun k hk L hL=> ?_⟩; have hx:= ht.2 k hk L hL; exact ⟨hx.reg,hx.coast,hx.commission,hx.merit⟩
    obtain ⟨W0,hψ,hΞ,hQ',H'⟩:= embalms M.K uB hvU O (Next.Foundations.chart G) (Next.Foundations.chart_ok G) (fun i=>(hi₁ i).trans (P.large i).need) hG z hz₁ J'
    refine ⟨W0,⟨hZ.1.trans (hL.trans hΞ),hZ.2.1.trans (hN₁.trans hψ),hZ.2.2.trans (hK.trans hQ')⟩,fun W ha hb hc a h hi=>?_⟩
    obtain ⟨T',B,hF,R,hR,b,T'',t,Xf,G,hX,hq,hsX,hFr,hπ,hπ',hXc,hLc,hXD,hβ₂⟩:= hW W (hL.trans (hΞ.trans ha)) (hK.trans (hQ'.trans hb)) (hN₁.trans (hψ.trans hc)) a h hi
    refine ⟨T',B,hF,R,hR,b,T'',t,Xf,G,hX,hq,?_⟩; intro C; refine ⟨hsX,hFr,hπ,hπ',hXc,hLc,hXD,fun F=>?_⟩
    obtain ⟨hC,hM,hA,hS,hL₀,S',hA,hC,h₃⟩:= hX.reception
    have hp:= Next.Rank.East.enclosing Xf hX.freight hM
    have hP:Paid W0 B.a:=retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid
    have hU:= H' C hP S' hC hM hp
    have hΓ:Trace.Terrace.supportQ B.a:= by
         apply Filter.Eventually.of_forall; intro i; rw[params_eq B.valid]; exact le_trans (by norm_num: (4:ℝ)≤100) (by change (_:ℝ) ≤ (s.profile _).supportExponent; rw[heSup.prices]; exact he _)
    let Alloy0: Alloy M P := Alloy.mk _ θ V' D W T' B
    have hNe:Quince.Ordeal B.a:=Quince.ordered (A:=Alloy0) (hβ _ (hV.trans hv))
    refine ⟨H C (retains_budget (hψ.trans hc) (fun i=>⟨hΞ i|>.trans (ha i),hQ' i|>.trans (hb i)⟩) B.valid) S' hC hM hp _ _ _ _ _ _ G hS F,?_⟩
    have hS0:=hΩ _ (hζ.trans hv) D W B.a B.valid; have hV1:=h3 _ (ht₄.trans (hV.trans hv)) D W B.a B.valid
    have htF:Trace.Terrace.Sceptre C K':= Quince.attain b T'' hX.nest hG hβ₂ hNe hM
    obtain ⟨L,hL⟩:= Ultrafilter.exists_le F.fuse
    obtain ⟨Tℓ,hT⟩:= Trace.Margin.agenda (t:=t) (U:=Xf) b hX.nest (hd _ _ (hcT.trans hv.beta) D W B.a B.valid) hV1 hΓ hG L (Trace.Terrace.link_mesh hL) (Trace.Terrace.link_period hL)
    exact Trace.Over.gang hM hG hS0 hq hS htF hΓ hL hT hS.costs.night (Filter.Eventually.of_forall (fun i=> hQ2 _)) (hV1 |> Trace.Margin.honor _) S' _ _ ht' hU
end YM.PhysicalNext.Repeat.Legato
