import YM.MSbar.Ballet.Wild
import YM.MSbar.Ballet.Cascade
import YM.MSbar.Ballet.Rain
import YM.MergeProof.East.Gran
import YM.MergeProof.North.Bourse


/-! Calendared proof thru actual Base+Seed. Can pay more beforeL, delays and Wait. -/
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
structure Estate {O:ChartRatio G}{K:MapPrices}{B:Sheet G}{D:Rolls B}{Θ:Protection D}{Y0:Delays Θ}{W:Bar Y0}{I:Wait W}{P:PostCost D}
     (i:G.ColorIndex)(F0:YM.MSbar.Heath.Voice G) (A:Directed G I O K P) : Prop where
    levy :YM.MSbar.Alto.Reports K B O A.a
    cart : YM.MSbar.Ballet.Load K B.kernel O A.a i F0
    sees :∀ m',A.a.clock.hatBeta (m'+1) ≤ 2*A.a.clock.hatBeta m'
    earns :∀ m' i,YM.MSbar.Mosaic.hatW (A.a.clock.hatBeta m')^4 ≤(A.a.S.side m' i).val
    holds : Tendsto (fun m=> (A.a.params m).order) atTop atTop
-- Another grantor for buying universal weak supplies. Can still extend before-L clocks, after-L Delays, extra Paid W and layouts. retains
variable (hG:G.Simple){K:KernelChoices}(hK :∀ p : Patch,p.Branches K G){v:Orders}(hp:ThroughLaunch.Draft v)(Q:ℕ→ℕ) (hQ:Monotone Q)(hQ':∀ i,1 ≤ Q i)
include hp hQ hQ' hK hG
lemma crestP (he:∀ i,100 ≤ v.supportExp i)(i:G.ColorIndex)(F0 : YM.MSbar.Heath.Voice G)(hF:YM.MSbar.Heath.Clear G F0): ∃ (s:Sheet G)(T:MapPrices)(Y:ℕ→ℝ)(K':Bid.Worth), s.kernel=K ∧ WithStage s v ∧ ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= ThroughLaunch.currency s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧Estate i F0 B∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),(X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J' ∧ Mallow.Hoard X.shape V')∧∃ (b:Bandage X Y K'), ∃ T t S D,Chateau b Q T t S D ∧ Stock.Tabs B.a ∧ (let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; Velour Z (renal B.a) (mutt B.a Q) D ∧ Tapestry Z (renal B.a) (mutt B.a Q) D ∧ ∀ f:Extraction.Order, CompleteWeak Z f) :=by
    obtain ⟨s,T,C,K,hP,hv,l,hL,hV⟩:=rainingP hG hK hp Q hQ hQ' he
    have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hv.jets]; exact (le_max_right ..).trans (hp.k i)) tendsto_id
    let K':= ThroughLaunch.bearing s T
    obtain ⟨p,hB⟩:=YM.MSbar.Ballet.paymentP (G:=G) K'
    refine ⟨s,T,C,K,hP,hv,l⊔p,hL.trans le_sup_left,fun k hk=>?_⟩; intro M; obtain ⟨hT,hh⟩:= sup_le_iff.mp hk; obtain ⟨hA,h₁⟩:=hV k hT; refine ⟨hA,fun P=>?_⟩; obtain ⟨w,H⟩:= h₁ P; refine ⟨w,fun w' hw Q E=>?_⟩; obtain ⟨F,H⟩:= H w' hw Q E; refine ⟨F,fun y hy=>?_⟩; obtain ⟨θ,hθ,H⟩:= H _ hy; refine ⟨θ,hθ,fun Q' K V0=>?_⟩
    have hr:=fun i=> hB i (P.L i) ((hh i).trans (P.large i).need)
    obtain ⟨Sa,hSa,hL'⟩:= YM.MSbar.Alto.album hG θ M.K M.O (fun i=>hr i|>.pre) V0 -- args?
    obtain ⟨B,h₁,h₂⟩:= YM.MSbar.Ballet.stage M.O M.K i F0 Sa hG (chart_ok G) hr hF
    obtain ⟨V₃,h₃,H₃⟩:=Mallow.loft B
    obtain ⟨V,hδ,H⟩:=H Q' K V₃
    refine ⟨V,hSa.trans (h₁.trans (h₃.trans hδ)),fun V' h D W=>?_⟩; obtain ⟨Z,hW,hZ⟩:=H V' h D W; refine ⟨Z,hW,fun W0 ha hb hc A hA hi=>?_⟩; obtain ⟨hB,B,hx,hq⟩:=hZ W0 ha hb hc A hA hi
    have hT:= hδ.trans h; have he':= H₃.1 _ hT _ _ _ B.valid
    have hp_: Tendsto (fun m=> (B.a.params m).order) atTop atTop:=by simp_rw [Push.PriceCompiler.params_eq B.valid]; exact ho.comp B.a.fits.deep
    exact ⟨hB,B,hx,⟨hL' V' (h₁.trans (h₃.trans hT)) D W0 _ B.valid,h₂ V' (h₃.trans hT) D W0 _ B.valid,he'.1,he'.2,hp_⟩,hq⟩
end YM.PhysicalNext.Repeat.Legato
