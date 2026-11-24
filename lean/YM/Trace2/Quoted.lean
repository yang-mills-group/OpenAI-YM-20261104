import YM.Trace2.Quota

-- Strengthening of `himalayas_columns`, retaining some actual prices during construction rather than assuming they accompany every Scaling.
set_option autoImplicit false
set_option maxHeartbeats 2800000
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ}

def QuotedWeak (C : Family G)(F : Extraction.Order):Prop:=∀ R,0<R→(standard C).Smooth → ∀ h:(standard C).RealSpin,
   ∃ b c:ℝ,0<b ∧ ∃ f:ℕ→ℕ,Tendsto f atTop atTop ∧ ∃ Y:ℕ→ℕ→ℕ→TableL C 4,
   Granular (fun i=>wok C 4 (f i) b c (Y i)) F h 2 R ∧ ∀ i,C.ref 4≤ f i∧ ∀ N p, f i<N→ Next.Rank.Price.Tested C 4 (f i) N p (Y i N p ⟨4,(by decide : 4<4+1)⟩)

section
variable {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ι → Tapes.Panel 4) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "S"=> standard C
variable (z:ℝ) (hZ : ∀ i≤4,Accent.generator G i≤ z)
variable {x y w:ι}{c:ℝ}
include H h hZ hp
lemma quoted_podium (F:Extraction.Order)(hn:2≤n)(g:Checks (P x).arc (P y).arc (P w).arc c n 4)
   (hw:∃ᶠ k in atTop,∃ Y,Poised P B H O J n z k Y) : QuotedWeak C F:=by
   intro R hr hs H'
   obtain ⟨f,hf,hh⟩:= extraction_of_frequently_atTop hw; choose Y hY using hh
   let a:= (P x).arc; have ha:0 < a:= by dsimp only [a]; have h:=(P x).huge; norm_num at h; linarith
   let K:= fun i=>wok C 4 (f i) a c (Y i); have hx(i):= w_right c F H' a (hY i)
   have he := hf.tendsto_atTop
   refine ⟨a,c,ha,f,he,Y,⟨⟨Eventually.of_forall (fun i=>(hx i).1),?_,?_,?_⟩,(Station.gap_rate A h a).comp he,fun m hm t ht v=>?_⟩,fun i=>?_⟩
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.1
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.2.1
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.2.2
   · exact aspect P B H h hp O J z hZ F hn R hr hs H' g t ht (depthWord t v) (hm.trans hn) he Y hY
   exact ⟨(hY i).early 4 le_rfl, fun N p hk=>(hY i).charts N p hk ⟨4,(by decide : 4<4+1)⟩ |>.1⟩
end
open Supply Accent
variable {T : Sheet G}{D': Rolls T} {E : Protection D'} {T' : Delays E}{K : Bar T'}
lemma quoted_sponsored (hG:G.Simple)(B:MapPrices)(O:HaarBudget G)(J:ChartRatio G)(hx:LocalRatio J) (u:ℕ→ℕ)(h:RelayP T B u) (hu:∀ i,u i ≤ (D'.L i).val) (U:Wait K) :∃ V:Wait K, U.minLength ≤ V.minLength∧U.readyHere ≤ V.readyHere ∧ U.window ≤ V.window ∧ ∀ C:Family G,Paid V C.path.levels→∀ H: Binding C,H.prices=B→ C.Makes→ParadeX C→∀ (W : Worth)(a b c e r L),Scrim C W a b c e (fly C.path.levels) r L→∀ F,CompleteWeak C F ∧ QuotedWeak C F:=by
    obtain ⟨b,P,ht,hP,hK⟩:=h.buys
    let Z j:= ∑ i∈Finset.range (j+1),Accent.generator G i
    have he(i):0 ≤ Accent.generator G i:=by unfold Accent.generator; positivity
    have ho i: 2 ≤ trays i:= Nat.le_add_left ..
    obtain ⟨V,P',h1,h2,h3,hC,hA,hB⟩:= y_stead B O J hG hK (μ:=Z) (fun i=>Finset.sum_nonneg fun j _=> he j) ho hu hx U hP
    refine ⟨V,h1,h2,h3,fun C hL H hz hM hu W a b c e r L hE f=>?_⟩
    have deduces (d:ℕ):=(ht d)
    have he'(d):∀ i≤d,generator G i≤Z d:= fun i hi=>Finset.single_le_sum (fun i _=> he i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    have hv (d): ∃ᶠ j in atTop,∃ Y, Poised (P' d) H hM O J (trays d) (Z d) j Y := by
       refine ((hB C hL H hz d).and_eventually (staging (n:=trays d) (z:=Z d) (P' d) H hM O J hG 0 hu (hA d 0))).mono fun i h => h.2 h.1.limit h.1.aisle
    constructor
    · intro N D R hR hT hS
      let d:= max N D; obtain ⟨c',ht⟩:= deduces d; rw [hC,hC,hC] at ht
      obtain ⟨V,hV⟩:= podium (P' d) H hM hG hE O J _ (he' d) f (ho d) R hR hT hS ht (hv d)
      exact reduce_wave V hS f hV (le_max_right ..) ((le_max_left ..).trans (Nat.le_add_right ..))
    obtain ⟨c',ht⟩:= deduces 4; rw [hC,hC,hC] at ht
    exact quoted_podium (P' 4) H hM hG hE O J _ (he' 4) f (ho 4) ht (hv 4)
end YM.MergeProof.East
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
lemma himalayas_quoted (he:∀ i,100 ≤ v.supportExp i): ∃ (s:Sheet G)(T:MapPrices)(Y:ℕ→ℝ)(K':Bid.Worth), s.kernel=K ∧ WithStage s v ∧ ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= ThroughLaunch.currency s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),(X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J')∧∃ (b:Bandage X Y K'), ∃ T t S D,Chateau b Q T t S D ∧ Stock.Tabs B.a ∧ (∀ d N p, t d ≤ N → Bandage.StackedColumns T (S d N p) (t d) K') ∧ Fridge (Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S) (far B.a) (fly B.a) ∧ (let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; Velour Z (renal B.a) (mutt B.a Q) D ∧ VelourArity Z (renal B.a) (mutt B.a Q) D ∧ ∀ f:Extraction.Order, (CompleteWeak Z f ∧ QuotedWeak Z f)) := by
    obtain ⟨s,T,Y,K',hs,hv,τ,hτ,hA⟩:= bally_columns hG hK hp Q hQ hQ' he
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
    obtain ⟨J',hd,hL,hK,H⟩:= quoted_sponsored hG M.K O (Next.Foundations.chart G) (Next.Foundations.chart_ok G) _ hz (fun i=>(hL i).trans (P.large i).need) Z
    refine ⟨J',⟨hZ.1.trans hL,hZ.2.1.trans hd,hZ.2.2.trans hK⟩,fun W ha hb hc a h hi=>?_⟩
    obtain ⟨T',B,hF,R,hR,b,T'',t,Xf,G,hX,hq,h_cols,h_fr,hπ⟩:= hW W (hL.trans ha) (hK.trans hb) (hd.trans hc) a h hi
    refine ⟨T',B,hF,R,hR,b,T'',t,Xf,G,hX,hq,h_cols,h_fr,?_⟩; intro C; refine ⟨hπ.1,hπ.2,?_⟩
    obtain ⟨hC,hM,hA,hS,hL₀,S',hA,hC,h₃⟩:= hX.reception
    have hp:= Next.Rank.East.enclosing Xf hX.freight hM
    exact H C (retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid) S' hC hM hp _ _ _ _ _ _ G hS
end YM.PhysicalNext.Repeat.Legato

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
-- Unconditional existence through the actual Wcmain, ranks and Seed.
variable (hG:G.Simple)
include hG
theorem noel_quotes {b:ℝ} (h:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    (∃ W r D, OPE.Package C W r D) ∧ (∀ f:Extraction.Order, MergeProof.East.QuotedWeak C f) ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= himalayas_quoted hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let M:=ThroughLaunch.currency s T l
  obtain ⟨⟨P⟩,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨U', -, hu'⟩ := OPE.halo_delay U
  obtain ⟨V,h₁,hK⟩:= hH Q J₀ U'
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T,t,S,D',hT,hq,h_col,h_fr,hu⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S
  change Velour Z (renal B.a) _ D' ∧ VelourArity Z _ _ D' ∧ (∀ f:Extraction.Order,(MergeProof.East.CompleteWeak Z f∧MergeProof.East.QuotedWeak Z f)) at hu
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S,rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu.1 hq hv hF,hq, Ribbons.fugacious Z hG hu.1⟩ -- fix argument order
  refine ⟨_,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hc,hF,hW, ?_, fun f=>(hu.2.2 f).2, hπ,fun f hf=>⟨grilled Z hF hU hq hf,(hu.2.2 f).1⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩
  · refine ⟨_, _, _, ⟨hU, hu.1, fun d N p hn m hm h => h_col d N p hn m hm h, h_fr, ?_, ?_, hv, hq⟩, hu.2.1⟩
    · apply hu' V h₁ Y B.a B.valid
    · assumption
end YM.PhysicalNext.Repeat.Legato

