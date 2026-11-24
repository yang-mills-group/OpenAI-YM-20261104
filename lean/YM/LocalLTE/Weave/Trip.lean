import YM.LocalLTE.Weave.Tourney
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
lemma tripPT (Ψ:Mallow.Prereq G) (v :Orders)(h :ThroughLaunch.Draft v){K:KernelChoices}(hK:∀ P:Patch,P.Branches K G)(p0 TT p':ℕ){ε δ:ℝ}(hε:δ<ε)(Wt:ClockB.Wind p0 δ)(hr:Wt.l< LocalLTE.Fan.Pastel.chip (p'+1)) (PB:ℕ→ℕ)(Θ:ℕ→ℕ→ℕ)(ζ:ℝ)(he:0<ζ)(ht:ζ<(p':ℝ)/100)(Ut:Involve G p' TT ζ Θ): ∃ s:Sheet G,∃ (T:MapPrices) (p: ℕ→ℝ)(W:Bid.Worth), s.kernel=K∧ ThroughLaunch.WithStage s v ∧ ∀ (_f:Tariffs)(X: Extra.Multi.Scope),∃ v: ℕ→ℕ, s.floorL ≤ v ∧
      ∀ k:ℕ→ℕ,v≤k→ Nonempty (Rolls (ThroughLaunch.raise s k))∧ ∀ D: Rolls (ThroughLaunch.raise s k), ∃ v : Return.Wages,∀ w:Return.Wages,v≤w→∀ (Q:ℕ→ℕ→ Postage)(E:ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff),∃ P: PostCost D,
      ∀ θ₀ : ℕ→ℝ,(∀ i,0<θ₀ i)→∃ θ: Protection D,θ.theta ≤ θ₀∧∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu)(J:ℕ→ℕ→JointLoad.Folio.Aux)(T0:Delays θ),∃ V:Delays θ,DelayLe T0 V ∧ OrderedDelays V∧∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I:Wait b)(a:Levels G)(_ : Paid I a),AsDivisors a.S →∃ (hp: Stock.Priced Y) (B: Directed G I (chart G) (ThroughLaunch.bearing s T) P),let A := (Alloy.mk P θ Y b I hp B : Alloy (ThroughLaunch.currency s T k) D); B.a=a∧ Extra.Multi.Prepared X ξ (localSection G) a ∧∃ R:Factor A,R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤(Q j i).rate)∧R.menu=H∧ R.auxiliary=J ∧ Nonempty (Bandage R p W) ∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ (∃ (M:Mallow.Funding R p0 ε)(W:Mallow.Trail M p')(_ :Adorn M W),  Mallow.Cready M W ∧ Ψ.jobs A.delay M.κ ∧ Mallow.Merchandise R.shape W.footprint W.ψ A.delay ∧ ∃ Z:Mallow.Wickets R.target p' ζ,Mallow.Bouquets R.shape Z M.κ Θ TT A.delay∧SuppliesQ M W Z Ut) ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
    obtain ⟨p,hp,h'⟩:= loch mile K h G
    obtain ⟨s,O,T,t,g,W,hS,hW,H⟩:= ThroughLaunch.sailsV hG hK h p hp
    refine ⟨s,T,p,W,hS,hW, fun f X=> ?_⟩
    obtain ⟨v,h⟩:= H f X
    obtain ⟨n,hn,hN⟩:= royaltyPT hG h (h' s hS hW) Ψ p0 p' hε Wt hr PB Θ TT ζ he ht Ut
    refine ⟨n,h.liftL.trans hn, fun k hk=> ⟨(hN k hk).1,fun D=> ?_⟩⟩
    obtain ⟨y,hy⟩:= (hN k hk).2 D; refine ⟨y,fun w hw Q E ξ=>?_⟩; obtain ⟨P,hP⟩:= hy w hw Q E ξ; refine ⟨P,fun θ₀ h₀=> ?_⟩; obtain ⟨θ,hα,hH⟩:= hP θ₀ h₀; exact ⟨θ,hα,fun H J T0 => hH H T0 J⟩

end YM.PhysicalNext.Repeat.Legato
