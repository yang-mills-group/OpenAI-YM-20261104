import YM.Integration.FVA1Physical.Round2.JointTrip
import YM.LocalLTE.Vinca.Trip
import YM.LocalLTE.Brochure.Company
import YM.LocalLTE.Georges.MarcoT
/-! Retain the purchased Qlocal program and kinetic archive on the C18 construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Round2
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow
variable {G:Gauge} (hG:G.Simple)
open YM.Qlocal.Schedule
variable {goal : Goal G} (buy : Obtainable goal)
include hG buy
lemma jointSpring (Ψ:Mallow.Prereq G) (m TT r:ℕ)(hp₀:LocalLTE.Fan.Pastel.chip (m+1)+1 < -(↑(r+1):ℝ)/2) {κ:ℝ}(hκ:0<κ)(U:Orders)(hU:ThroughLaunch.Draft U) (b₀:ℝ)(Θ:ℕ→ℕ→ℕ) (ζ:ℝ)(he:0<ζ) (σ:ℝ)(hσ:(↑(r+1):ℝ)/2<σ)(ht:ζ<(m:ℝ)/100)(Ft: Involve G m TT ζ Θ)(l:ℕ)(F₀:Elixir G m): ∃ (X:Metals G)(D:Rolls X.p)(A:Alloy X D)(R:Factor A),goal X D A R ∧ Extension.UV.Archive A.B ∧ A.B.a.clock.kernel.penalty=κ∧ b₀≤A.B.a.clock.bar∧WithStage X.p U ∧ Mallow.Outlook r m A.delay ∧ (∃ f K, Nonempty (Bandage R f K)∧ Elevates A.B.a f K l ∧ (∀ i j,(R.target i j).halo=500)) ∧ MintZ A.delay σ r ∧ ∃ p0:ℕ,∃(F:Mallow.Funding R p0 1)(M:Mallow.Preview F)(W:Trail F m)(_V:Cready F W)(_D:Adorn F W),∃ P:Bolt A, Mallow.Made F W M P∧ Ψ.jobs A.delay F.κ ∧ Mallow.Merchandise R.shape W.footprint W.ψ A.delay ∧ ∃ Z:Mallow.Wickets R.target m ζ,Mallow.Bouquets R.shape Z F.κ Θ TT A.delay∧SuppliesQ F W Z Ft∧ Fulfilled F₀ F W:=by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G κ hκ
  obtain ⟨p0,hv,⟨Wt⟩,hx⟩:= Mallow.sailing m (1/2) (by norm_num) r
  obtain ⟨s,T,C,K,hs,hV,hC⟩:= jointTrip hG buy Ψ U hU hp p0 TT m (show (1/2:ℝ)<1 by norm_num) Wt (hx _) (fun _=>1) Θ ζ he ht Ft l F₀
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
  obtain ⟨hP,B,hA,hS,R,-,-,-,-,-,hx0,hxS,hxV,-,-,-,⟨X',W,P',H',hK'⟩,paid,archive,hF⟩:= hT U₂ (hu₁.trans hu₂) b I _ ha hD
  obtain ⟨M⟩:= Mallow.previews X'; obtain ⟨T,hT⟩:= Mallow.emerging X' W H' M P' hG
  refine ⟨_,_,_,R,paid,archive,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hs)).trans hb, ?_, ⟨hV.first,hV.jets,hV.powers,hV.prices⟩,(H₁ _ hu₂),⟨_,_,hx0,hxS,hxV⟩,(H₂ _ (DelayLe.refl _)),p0,X',M,W,H',P',T,hT,hK'⟩
  change b₀≤ B.a.clock.bar; exact hb'.trans_eq B.valid.bar.symm
end YM.PhysicalNext.Repeat.Legato.Round2
