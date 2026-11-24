import YM.OPE.Compatible.Niche.Turns
import YM.OPE.Compatible.Niche.Fur
import YM.OPE.Compatible.Calendars.Again
import YM.OPE.Columns.Ledger
import YM.OPE.Compatible.Brou.Bands
/-!
# Producer with additional quantitative supplies

An alternative in the style of OPE/Columns/Ledger, etc. Supplies through
order 2 pricing for the log proof, still buys the realization on any
permitted generation with raised delays. New here is in particular the
beat (see `Exodus`). Can still combine with the later clocks for opacity
and get both estimates on *one* data set (`Clients/Jacob`). No reliance on
accounting imported as axioms from the manuscript.
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
open YM.MergeProof.East
-- Another grantor for buying universal weak supplies. Can still extend before-L clocks, after-L Delays, extra Paid W and layouts.
open OPE.Owl OPE
variable (hG:G.Simple){K:KernelChoices}(hK :∀ p : Patch,p.Branches K G){v:Orders}(hp:ThroughLaunch.Draft v)(Q:ℕ→ℕ) (hQ:Monotone Q)(hQ':∀ i,1 ≤ Q i)
variable {M:Metals G}{P: Rolls M.p}
section
set_option quotPrecheck false
variable {H: Votive.Sponsor G}{A: Votive.Seasons H}{g:G.Simple}{a:Axis}
variable {s: Sheet G}{T:MapPrices}{t:ℕ→ℕ}
local notation "P0"=> ThroughLaunch.raise s t
local notation "M✳"=> ThroughLaunch.currency s T t
variable {D : Rolls (ThroughLaunch.raise s t)}{L:Stroke.PriceBook (Next.Foundations.chart_ok G) A}
-- consumption properties; note explicit support/arity and other cost hypotheses
structure Yarn (M:Metals G) {P:Rolls M.p}(W:Alloy M P){X:Factor W}{C:ℕ→ℝ}{K:Bid.Worth}(b:Bandage X C K)(Q:ℕ→ℕ)(T:Bolt W)(t:ℕ→ℕ)(Y:∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail T) N p) (D:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail T).rep N p (m+1)) ((Issue.trail T).rep N p m)):Prop where
       placed : Chateau b Q T t Y D
       tabs : Stock.Tabs W.B.a
       columns : ∀ d N p, t d ≤ N → Bandage.StackedColumns T (Y d N p) (t d) K
       landed: let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t Y; Fridge Z (far W.B.a) (fly W.B.a) ∧ Velour Z (renal W.B.a) (mutt W.B.a Q) D∧VelourArity Z (renal W.B.a) (mutt W.B.a Q) D ∧ TicketReady Z (renal W.B.a) (mutt W.B.a Q) D ∧ (∀ f: Extraction.Order, CompleteWeak Z f)
       halo : OPE.HaloGate W.B.a
variable (A0:Desk (ThroughLaunch.raise s t) L a g)(H':Spells.Pad G) (Y:ℕ→ℝ)(K':Bid.Worth)
structure Exodus (W:Alloy (ThroughLaunch.currency s T t) D) (V:Factor W) (B:Bolt W)(S:Bandage V Y K')(t0:ℕ→ℕ) (X:∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail B) N p) (Dt:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail B).rep N p (m+1)) ((Issue.trail B).rep N p m)): Prop where
       costE : BeatV A0 H' W.θ V.books W.delay
       analysisK : TowerCap (M:=ThroughLaunch.currency s T t) W.θ W.delay
       turtle: Torrent (s:=s) H.X T H.l W.post W.B.a W.B.M W.B.kin
       hold : Yarn M✳ W S Q B t0 X Dt
end
include hp hQ hQ' hK hG
lemma producerB (he:∀ i,100 ≤ v.supportExp i) :
   ∃ (s:Sheet G)(T:MapPrices)(H: Votive.Sponsor G) (A: Votive.Seasons H)
     (L:Stroke.PriceBook (Next.Foundations.chart_ok G) A)(Y:ℕ→ℝ)(K':Bid.Worth),
       s.kernel=K∧Votive.Lend s A ∧ WithStage s v ∧
       ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= ThroughLaunch.currency s T k;
       ∀ (α:Axis), Nonempty (Owl.Desk M.p L α hG) ∧
       ∀ (X:Owl.Desk M.p L α hG)(P:Rolls M.p)(Kx:Spells.Pad G),Owl.FrameBill X P →
       ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→
       ∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange),
       ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧
       ∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),
       ∃ V:Delays θ,DelayLe T0 V∧∃ Yc:Arms (M:=M) P,∀ V':Delays θ,
       DelayLe V V'→∀ (D:Bar V') (W:Wait D),
       ∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧
       ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→
       ∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F), B.a=a ∧
       ∃ (X': Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),
           (X'.books=Yc∧ X'.walls=w∧ X'.exchange=E∧ (∀ j i,(X'.book j i).rate ≤ (Qt j i).rate)∧
             X'.menu=Ht∧ X'.auxiliary=J')∧∃ (b:Bandage X' Y K'),
             ∃ T t S D', Exodus Q X Kx Y K' (Alloy.mk F θ V' D W' h B) X' T b t S D' := by
       obtain ⟨s,T0,U0,t,Y,K',⟨X,b,hB,hΦ⟩,hF,Hs,τ,hT,H⟩:= himalayas_tokenQ hG hK hp Q hQ hQ' he
       let V:Votive.Sponsor G:= ⟨K,U0,t,X,b,hB,hK⟩
       obtain ⟨A,hW,hL,L⟩:= Stroke.forge V (Next.Foundations.chart_ok G) hG (fun i=> (s.profile i).width) (fun i=>(s.profile i).paths) (fun i=> (s.profile i).width_pos)
       have hO:Tendsto (fun i=> (s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [Hs.jets]; exact (le_max_right ..).trans (hp.k i)) tendsto_id
       refine ⟨s,T0,V,A,L,Y,K',hF,⟨hF,hΦ,hW,hL⟩,Hs,τ,hT,?_⟩
       intro k hk M a
       refine ⟨Owl.Desk.from_a A L M.p hO a hG, ?_⟩
       intro D p R hD
       obtain ⟨u,hu⟩:= (H k hk).2 p
       refine ⟨u,fun w hw Q E=> ?_⟩
       obtain ⟨F,hF⟩:= hu w hw Q E
       refine ⟨F,fun T h_ask=>?_⟩
       obtain ⟨θ,hθ,H'⟩:=hF T h_ask
       refine ⟨θ,hθ,fun Ht J Tx=>?_⟩
       obtain ⟨U,ht,hH⟩:= OPE.halo_delay Tx
       obtain ⟨U',hu,Yc,hP⟩:= H' Ht J U
       obtain ⟨Z,hV,hK⟩:=Owl.Rhythm D R θ Yc hD U'
       obtain ⟨U₁,hV₁,hV₂⟩:= Owl.TowerCap.grind θ Z (M:=M)
       refine ⟨U₁, ht.trans (hu.trans (hV.trans hV₁)),Yc,fun V hV' D0 W=>?_⟩
       obtain ⟨W',hp,H⟩:= hP _ (hV.trans (hV₁.trans hV')) D0 W
       refine ⟨W',hp,fun W0 h0 h1 h2 a h hh=>?_⟩
       obtain ⟨hR,B',hX,hA,M0,Hm,T',Vb,t,S',d,Phe,h_tabs,h_col,h_fr,hU⟩:=H W0 h0 h1 h2 a h hh
       refine ⟨hR,B',hA,M0,Hm,T',Vb,t,S',d, ⟨?_,hV₂ _ hV',hX,Phe,h_tabs,h_col,⟨h_fr,hU⟩,hH V (hu.trans (hV.trans (hV₁.trans hV'))) W0 _ B'.valid ⟩⟩
       exact Hm.1.symm ▸ hK _ (hV₁.trans hV')
end YM.PhysicalNext.Repeat.Legato
