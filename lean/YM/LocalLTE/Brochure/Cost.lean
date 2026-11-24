import YM.LocalLTE.Brochure.Tourney
import YM.Branch.Pick
/-! Genuine selected Bolts, capacities all m. No marked estimates yet. Does not choose this Bolt using another production! Exposes more options via liftsB. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow
variable {G:Gauge} (hG:G.Simple)
include hG
lemma tripT (Ψ:Mallow.Prereq G) (v :Orders)(h :ThroughLaunch.Draft v){K:KernelChoices}(hK:∀ P:Patch,P.Branches K G)(p0 TT p':ℕ){ε δ:ℝ}(hε:δ<ε)(Wt:ClockB.Wind p0 δ)(hr:Wt.l< LocalLTE.Fan.Pastel.chip (p'+1)) (PB:ℕ→ℕ)(Θ:ℕ→ℕ→ℕ)(ζ:ℝ)(he:0<ζ)(ht:ζ<(p':ℝ)/100): ∃ s:Sheet G,∃ (T:MapPrices) (p: ℕ→ℝ)(W:Bid.Worth), s.kernel=K∧ ThroughLaunch.WithStage s v ∧ ∀ (_f:Tariffs)(X: Extra.Multi.Scope),∃ v: ℕ→ℕ, s.floorL ≤ v ∧
      ∀ k:ℕ→ℕ,v≤k→ Nonempty (Rolls (ThroughLaunch.raise s k))∧ ∀ D: Rolls (ThroughLaunch.raise s k), ∃ v : Return.Wages,∀ w:Return.Wages,v≤w→∀ (Q:ℕ→ℕ→ Postage)(E:ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff),∃ P: PostCost D,
      ∀ θ₀ : ℕ→ℝ,(∀ i,0<θ₀ i)→∃ θ: Protection D,θ.theta ≤ θ₀∧∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu)(J:ℕ→ℕ→JointLoad.Folio.Aux)(T0:Delays θ),∃ V:Delays θ,DelayLe T0 V ∧ OrderedDelays V∧∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I:Wait b)(a:Levels G)(_ : Paid I a),AsDivisors a.S →∃ (hp: Stock.Priced Y) (B: Directed G I (chart G) (ThroughLaunch.bearing s T) P),let A := (Alloy.mk P θ Y b I hp B : Alloy (ThroughLaunch.currency s T k) D); B.a=a∧ Extra.Multi.Prepared X ξ (localSection G) a ∧∃ R:Factor A,R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤(Q j i).rate)∧R.menu=H∧ R.auxiliary=J ∧ Nonempty (Bandage R p W) ∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ (∃ (M:Mallow.Funding R p0 ε)(W:Mallow.Trail M p')(_ :Adorn M W),  Mallow.Cready M W ∧ Ψ.jobs A.delay M.κ ∧ Mallow.Merchandise R.shape W.footprint W.ψ A.delay ∧ ∃ Z:Mallow.Wickets R.target p' ζ,Mallow.Bouquets R.shape Z M.κ Θ TT A.delay) ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
    obtain ⟨p,hp,h'⟩:= loch mile K h G
    obtain ⟨s,O,T,t,g,W,hS,hW,H⟩:= ThroughLaunch.sailsV hG hK h p hp
    refine ⟨s,T,p,W,hS,hW, fun f X=> ?_⟩
    obtain ⟨v,h⟩:= H f X
    obtain ⟨n,hn,hN⟩:= royaltyT hG h (h' s hS hW) Ψ p0 p' hε Wt hr PB Θ TT ζ he ht
    refine ⟨n,h.liftL.trans hn, fun k hk=> ⟨(hN k hk).1,fun D=> ?_⟩⟩
    obtain ⟨y,hy⟩:= (hN k hk).2 D; refine ⟨y,fun w hw Q E ξ=>?_⟩; obtain ⟨P,hP⟩:= hy w hw Q E ξ; refine ⟨P,fun θ₀ h₀=> ?_⟩; obtain ⟨θ,hα,hH⟩:= hP θ₀ h₀; exact ⟨θ,hα,fun H J T0 => hH H T0 J⟩

lemma volantT (Ψ:Mallow.Prereq G) (m TT r:ℕ)(hp₀:LocalLTE.Fan.Pastel.chip (m+1)+1 < -(↑(r+1):ℝ)/2) {κ:ℝ}(hκ:0<κ)(U:Orders)(hU:ThroughLaunch.Draft U) (b₀:ℝ)(Θ:ℕ→ℕ→ℕ) (ζ:ℝ)(he:0<ζ) (σ:ℝ)(hσ:(↑(r+1):ℝ)/2<σ)(ht:ζ<(m:ℝ)/100): ∃ (X:Metals G)(D:Rolls X.p)(A:Alloy X D)(R:Factor A),A.B.a.clock.kernel.penalty=κ∧b₀≤A.B.a.clock.bar∧WithStage X.p U ∧ Mallow.Outlook r m A.delay ∧ MintZ A.delay σ r ∧ ∃ p0:ℕ,∃(F:Mallow.Funding R p0 1)(M:Mallow.Preview F)(W:Trail F m)(_V:Cready F W)(_D:Adorn F W),∃ P:Bolt A, Mallow.Made F W M P∧ Ψ.jobs A.delay F.κ ∧ Mallow.Merchandise R.shape W.footprint W.ψ A.delay ∧ ∃ Z:Mallow.Wickets R.target m ζ,Mallow.Bouquets R.shape Z F.κ Θ TT A.delay:=by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G κ hκ
  obtain ⟨p0,hv,⟨Wt⟩,hx⟩:= Mallow.sailing m (1/2) (by norm_num) r
  obtain ⟨s,T,C,K,hs,hV,hC⟩:= Legato.tripT hG Ψ U hU hp p0 TT m (show (1/2:ℝ)<1 by norm_num) Wt (hx _) (fun _=>1) Θ ζ he ht
  let u:Tariffs:=⟨fun _=>0,fun _=>le_rfl,fun _=>1⟩; let X:Extra.Multi.Scope:=⟨fun _=>1,fun _=>0,fun _=>1,fun _=>le_rfl,fun _=>Nat.zero_lt_one⟩
  obtain ⟨v,hv,H⟩:=hC u X; obtain ⟨⟨P⟩,hc⟩:= H v le_rfl; obtain ⟨w,hw⟩:=hc P
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩; let Y : Extra.Multi.Tariff:=⟨1,0,fun _=>le_rfl⟩
  obtain ⟨F,h⟩:= hw w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=>E) Y
  obtain ⟨θ,-,h⟩:= h _ (fun _=>one_pos)
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  obtain ⟨V,hV',hO,hT⟩:= h Q J ⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩
  obtain ⟨U₁,hu₁,H₁⟩:= Mallow.forecast r m hp₀ V
  obtain ⟨U₂,hu₂,H₂⟩:= Mallow.pocketsZ r σ hσ U₁
  obtain ⟨b,hb'⟩:= Bar.exists_above U₂ b₀
  let I:Wait b:=⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩; obtain ⟨a,ha,hD⟩:=Wait.engine I hG
  obtain ⟨hP,B,hA,hS,R,-,-,-,-,-,-,-,-,-,⟨X',W,P',H',hK'⟩,hF⟩:= hT U₂ (hu₁.trans hu₂) b I _ ha hD
  obtain ⟨M⟩:= Mallow.previews X'; obtain ⟨T,hT⟩:= Mallow.emerging X' W H' M P' hG
  refine ⟨_,_,_,R,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hs)).trans hb, ?_, ⟨hV.first,hV.jets,hV.powers,hV.prices⟩,(H₁ _ hu₂),(H₂ _ (DelayLe.refl _)),p0,X',M,W,H',P',T,hT,hK'⟩
  change b₀≤ B.a.clock.bar; exact hb'.trans_eq B.valid.bar.symm

end YM.PhysicalNext.Repeat.Legato
