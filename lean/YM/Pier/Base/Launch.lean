import YM.OPE.Vitrines.Funding
import YM.RG17.Feather
import YM.Pier.Reserve.Entries
/-!
# Supporting both the RG17 Run (FullVolume.Jewel with all admitted periods) and
# the stronger OPE configurations. Single physical choice.

Not combining two legacies and claiming their conjectural sets intersect.
Produce the stronger Vitrines reserves for the native FullVolume field stock
(from the price proof on each step); simultaneously schedule space and time to
meet the premises of Strobe.Citizen. From RG17 Feather constructor. Keep a
post-L Delay hook accessible for prescribing further sharpenings.
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

/-- No purported polynomial uniformity of post-L constants -- the caller must
show compatibility through all required profiles/delays. -/
def OnPier (S : Levels G → Prop) : Prop :=
  ∀ (s:Sheet G) (P:Rolls s) (Y:Protection P) (U:Delays Y), ∃ V:Delays Y,
    DelayLe U V ∧ ∀ W:Delays Y, DelayLe V W → ∀ (D:Bar W) (Q:Wait D) (K:Levels G),
    Paid Q K → S K
lemma clearPier (G:Gauge) : OnPier (fun _ : Levels G => True) := by
    intro s P Y V; exact ⟨V,DelayLe.refl _,fun _ _ _ _ _ _=>trivial⟩
variable (P0 : Levels G → Prop) (hP : OnPier P0)
include hP
-- Unconditional existence through the actual Wcmain, ranks and Seed.
variable (hG:G.Simple)
include hG
theorem factorShipPier {β:ℝ} (h:0<β) : ∃ (M:Metals G)(P:Rolls M.p)(A:Alloy M P)(X:Factor A)(Y:ℕ→ℝ)(K:Bid.Worth)(b:Bandage X Y K),
    Stationary.Artes.Cadre A.post A.B.kin ∧ Next.Free.Amplify A.B.M ∧ Jams.Wild X.shape A.delay ∧ A.B.a.clock.kernel.penalty=β ∧ Flick A.B.a ∧ OPE.Therm.Poetry A.B.a ∧ Subsidize A.B.a ∧ P0 A.B.a ∧ Ahead b (fun i=>i+1) ∧ Mallow.AccordV X.shape (fun i=>i+1) A.delay ∧ OPE.HaloGate A.B.a ∧ Unlatched b (fun i=>i+1) (fun T t S _ => let Z := Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∃ h:Z.Makes, SharpGram.Dense.Coverage Z h) ∧ ∃ ξ t τ a, ∃ (V:Roof.Lyrics X t t), Muse.Plato V ξ a a τ ∧ ∃ θ1:Luna.Tableau ξ 300,Jams.PaysW X.shape a A.delay ∧ Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay ∧ (∀ i:ℕ,(A.B.a.budget i).supportExponent=100) ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) ∧ ∃ UX,FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 UX P.L ∧ Mallow.Canyon ξ X.shape Y θ1 UX A.delay := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G β h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun _=>100⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= le_rfl
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    exact le_rfl
  obtain ⟨q,hq⟩:=Muse.concert.exists
  obtain ⟨θ1⟩:= Luna.Tableau.access 300 (show 1≤q by linarith [hq.1])
  let a':ℝ:= 1/1024; have hh:0<a':=by norm_num [a'];
  obtain ⟨t,ht,hu,hU⟩:=Jams.ball_on (q:=q) (s:=a') (r:=1) (by linarith [hq.1]) hh (by norm_num [a']) (by norm_num)
  obtain ⟨s,T,Y,K,hX,WStage,l,hL,hK⟩:= freakFare17 hG hp he (fun i=>i+1) (fun i j he=>Nat.add_le_add_right he 1) (by intro i; omega) θ1 hU hE
  have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [WStage.jets]; exact (le_max_right ..).trans (he.k i)) tendsto_id
  obtain ⟨R,hR⟩:= Pert.Dense.bulletin s (ThroughLaunch.raging s T) ho
  obtain ⟨O⟩:= Next.Rank.exists_budget G
  let M:=ThroughLaunch.bountyV s T (l⊔R)
  obtain ⟨⟨P⟩,H⟩:= hK (l⊔R) le_sup_left
  have hz : Pert.Dense.Relay M.p M.K R:=by
     obtain ⟨b,F,ψ,he,v⟩:= hR.bulletin
     refine ⟨b,F,ψ,he,v.same,?_,?_,?_⟩
     · intro i; exact ⟨(v.buys i).1,(v.buys i).2⟩
     · intro i; exact ⟨(v.shops i).1⟩
     intro i d j;exact v.lifts i d j
  have hUQ :∀ i,R i ≤ (P.L i).val:=fun i=>(le_sup_right (a:=l) (b:=R) i).trans (P.large i).need
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩
  obtain ⟨Ugate,-,hgate⟩ := OPE.halo_delay U
  obtain ⟨Ustep,hStep,hstep⟩:= flickDelay Ugate
  obtain ⟨U1,h1,hPo⟩:= OPE.Therm.poetry_delay Ustep
  obtain ⟨U2,h2,hSu⟩:= subsidize_feasible U1
  obtain ⟨U3,h3,hEx⟩:= hP _ P θ U2
  obtain ⟨V,h₁,hK⟩:= hH Q J₀ U3
  obtain ⟨V',H',Hp'⟩:=Tent.quotes V hh
  obtain ⟨Vx,hx,hV⟩:=Muse.header hG V' hh q
  obtain ⟨D,-⟩:= Bar.exists_above Vx 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y0,-,H⟩:= hK Vx (H'.trans hx) D I
  let W0 : Wait D:= ⟨fun _ => 0,SharpGram.Dense.slim D,SharpGram.Dense.slimWindow hG D,0⟩
  obtain ⟨W2,_,hSlim,WP,hWP⟩ := Pert.Dense.slim_wait_for M.K O (Next.Foundations.chart G) W0 hG hz hUQ (Next.Foundations.chart_ok G) rfl
  obtain ⟨Y,hYT,hLate⟩:= SharpGram.Dense.loadBoth hG Y0 W2
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,hU⟩:= H Y hYT.ready hYT.range hYT.minL a ha hp
  obtain ⟨hA,hC,hM,hη,hW,hL,hU',hE,hR,hCσ,hPΩ,U₁,HΩ,hYe,hYv,hY₁,hYs,hAr⟩:=W
  have ht':= Hp' Vx hx
  obtain ⟨p,hh'⟩:= Tent.verses R ht' hR hE
  have hExp (i:ℕ): (B.a.budget i).supportExponent=100 := by
    change (B.a.params i).supportExponent=100; rw [params_eq B.valid]; exact WStage.prices _
  have htv:= h₁.trans (H'.trans hx)
  have hs2:= h3.trans htv
  have hs1:= h2.trans hs2
  have hsp:= h1.trans hs1
  refine ⟨_,_,_,_,_,_,c,hCσ,hPΩ,hYs,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hstep Vx hsp _ _ B.a B.valid,hPo Vx hs1 Y B.a B.valid,hSu Vx hs2 Y B.a B.valid,hEx Vx htv D Y B.a B.valid,hU,hAr,hgate Vx (hStep.trans hsp) Y B.a B.valid, ?_, q,t,a',a',p,⟨hL,hU',by norm_num [a', FullVolume.Amp.glint],hq, ht', hR,hB.symm ▸ hV Vx (DelayLe.refl _) D Y a ha,by norm_num [a', FullVolume.Amp.glint],hh',hG, Drifting.pay B.valid⟩,θ1,U₁,HΩ,hExp,hYv,hY₁⟩
  intro t u S v Xf K C hx hp ht
  obtain ⟨hX,hq,hπ,hv,hS,hn,hL',-⟩:= hU t u S v Xf K hx hp ht; refine ⟨hX,hq,hπ,hv,hS,hn,hL',?_⟩
  obtain ⟨hC,hM,hA,hS,hL₀,S',hA,hC,h₃⟩:= hX.reception
  exact ⟨hM,SharpGram.Dense.covered M.K O (Next.Foundations.chart G) WP hWP hSlim hLate B.valid S' hC hM (Next.Rank.East.enclosing Xf hX.freight hM)⟩

end YM.PhysicalNext.Repeat.Legato
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set MeasureTheory Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse
namespace Campaign
set_option quotPrecheck false
open Boutique
open Boutique
section
variable {M : Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:ℕ→ℝ}{K:Bid.Worth}{b:Bandage X Y K}
/- Construction independent of p sampling. k>=1. later reserve may request hard-limit recipe. -/
lemma pillarPier (h:G.Simple){q:ℕ→ℕ}(hh:Ahead b q) (hQ:Mallow.AccordV X.shape q A.delay)(hU:Unlatched b q (fun T t S _ => let Z := Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∃ h:Z.Makes, SharpGram.Dense.Coverage Z h)){c u t τ:ℝ}{L: Roof.Lyrics X u u}(Φ:Muse.Plato L c t t τ) (hP : Stationary.Artes.Cadre A.post A.B.kin)(he : Next.Free.Amplify A.B.M)(hy:Jams.Wild X.shape A.delay)(θ1:Luna.Tableau c 300) (v:ℕ→ℕ→ℝ)(hν:Jams.PaysW X.shape t A.delay)(hΩ:Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay)(hPγ:FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 v P.L) (hv:∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent)(hψ:∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) (hG:Mallow.Canyon c X.shape Y θ1 v A.delay):∃ (R:Run G)(T:Campaign R), Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay ∧ Nonempty (Pillars R T)  ∧ R.Q=q ∧ R.family.path.levels=A.B.a ∧ Mallow.AccordV R.kit.shape R.Q R.alloy.delay ∧ SharpGram.Dense.Coverage R.family R.makes ∧ ∃ Θ, Sky R T Θ v :=by
    let C:=b
    choose s hp using fun d:ℕ=> ((eventually_ge_atTop 1).and (A.B.a.fits.deep.eventually_ge_atTop (d+3))).exists
    have hb (d): 1 ≤ s d:= hp d|>.1
    obtain ⟨T,⟨Z⟩,hD⟩:= FullVolume.rodB X Φ
    let ht(d):d+3 ≤ (Issue.trail T).levels.clock.J (s d):= hp d|>.2
    have hZ:=Z.receipts
    choose B hB using fun N p m (hm : m < N)=> Boutique.taste h (F₀:=L) hZ (hD N p) hm
    let U (N p:ℕ):Branch X T.history N p 0 := ⟨T.choice,fun i _ hm=> hZ.samples h _ _ _ hm,fun m _ he=> B N p m he⟩ -- dots need explicit
    obtain ⟨V,hC,hY,H⟩:= Bandage.coming h b hZ s ht U; let R : Run G:= ⟨M,P,A,X,Y,K,b,q,hh,T,Z,s,ht,ease U,V,hC,fun N m p hx=> Boutique.mountain T (B N p m hx),hY⟩
    let T':Campaign R:= ⟨c,τ,u,t,L,Φ,hD⟩; obtain ⟨-,-,-,-,-,-,-,z,hz⟩:= hU T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books; exact ⟨R,T',⟨hP,he⟩,hy,⟨hb,U,rfl,fun N p m hm=> hB N p m hm,H⟩,rfl,rfl,hQ,hz,θ1,⟨hv,hψ,hν,hΩ,hPγ,hG⟩⟩
end

variable (P0 : Levels G → Prop) (hP : OnPier P0)
include hP
set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
/-- This is the single physical clock. -/
theorem buildsPier (h:G.Simple) (w:ℝ) (hw:0<w):
    ∃ (R:Run G)(T:Legato.Campaign R)(_W:Pillars R T),
      Locrian R ∧ Jams.Wild R.kit.shape R.alloy.delay ∧
      R.family.path.levels.clock.kernel.penalty=w ∧ P0 R.family.path.levels ∧
      Mallow.AccordV R.kit.shape R.Q R.alloy.delay ∧ OPE.HaloGate R.family.path.levels ∧
      SharpGram.Dense.Coverage R.family R.makes ∧ Flick R.family.path.levels ∧
      Citizen R.family R.w (mutt R.family.path.levels R.Q) R.doors ∧
       ∃ v:ℕ→ℕ→ℝ, ∃ Θ, Sky R T Θ v:=by
   obtain ⟨X,P,A,F,L,Q,b,hY,hC,hYs,hW,hFlick,hPo,hSu,hEx,hH,hAr,hGate,hdens,
     ξ,v,t,a,D,Φ,θ1,hν,hφ,hv,hψ,UΩ,hP,hZ⟩ := factorShipPier P0 hP h hw -- arg order
   obtain ⟨R,T,hx,hp,⟨W⟩,hB,hL,hQ,hc,Θ,hγ⟩:= pillarPier h hH hAr hdens Φ hY hC hYs θ1 UΩ
     hν hφ hP (fun i=>(hv i).ge) hψ hZ
   rw [← hL] at hW hFlick hPo hSu hEx hGate hv
   have hS := Campaign.opePackage17 W h hQ hGate hγ
   obtain ⟨ht,-⟩:= R.bought _ R.tuning.receipts _ R.accepts _ _ R.makes R.carries R.books
   refine ⟨R,T,W,hx,hp,hW,hEx,hQ,hGate,hc,hFlick,⟨⟨hS,?_,hv,?_⟩,?_,hPo⟩,_,_,hγ⟩
   · exact fun m N j d => further h R.b R.Q _ _ _ R.doors ht hSu m N j d
   · rw [hB]; exact ((tendsto_add_atTop_nat 1).comp
       (R.alloy.B.a.fits.deep.comp (tendsto_add_atTop_nat 1)))
   exact fun d N p m hm hn b=> (fitsPier W h hm hn b).regular
end Campaign
end YM.PhysicalNext.Repeat.Legato
