import YM.Integration.ChronPreconstruction.ConstructionTreasury
import YM.Integration.RG05Preconstruction.PeriodClock

/-! Preserve a predicated purchase on the very Bandage used to construct the Wilson run. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
open YM.Integration.RG05Preconstruction
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
open Campaign
set_option quotPrecheck false
open Boutique
open YM.Integration.WilsonLimitConstruction
section
variable {M : Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:ℕ→ℝ}{K:Bid.Worth}{b:Bandage X Y K}
/- Construction independent of p sampling. Again from DensityClock.lean. -/
lemma ReporterRoofs.engage (Ω : RemainderComparison.Chron.Contemple G) (ℋ : CustodyR G) (h:G.Simple){q:ℕ→ℕ} (Δ : Daisy.Charity.RG12.Decal G) (hQs:Tendsto q atTop atTop)
    (hU:Attentive b q) (hQ:Mallow.AccordV X.shape q A.delay) (hBa: YM.Integration.RG05Preconstruction.Extras Ω Δ b) (hYf:Mallow.FrameAccord X.target P A.delay)
    (h100:∀ i,(A.B.a.params i).supportExponent = 100){c u t τ:ℝ}{L: Roof.Lyrics X u u}(Φ:Muse.Plato L c t t τ) (hP : Stationary.Artes.Cadre A.post A.B.kin)(he : Next.Free.Amplify A.B.M)(hy:Jams.Wild X.shape A.delay)(θ1:Luna.Tableau c 300) (v:ℕ→ℕ→ℝ)(hcR:ℋ.items A.post Y K θ1 A.B.a)(hν:Jams.PaysW X.shape t A.delay)(hΩ:Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay)(hPγ:FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 v P.L) (hv:∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent)(hψ:∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) (hG:Mallow.Canyon c X.shape Y θ1 v A.delay)
    (prediction : FundedCompanySelection.Prediction G) (hPrediction : prediction X)
    (license : ∀ {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {X:Factor A} {Y:ℕ→ℝ} {K:Bid.Worth}, Bandage X Y K → Prop)
    (purchased : license b) :
    ∃ (R:Run G)(T:Campaign R), prediction R.kit ∧ license R.b ∧ R.metals = M ∧ Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay ∧ Nonempty (Pillars R T)  ∧ R.family.path.levels=A.B.a ∧ Mallow.AccordV R.kit.shape R.Q R.alloy.delay ∧
      YM.Integration.RG05Preconstruction.Extras Ω Δ R.b ∧ Attentive R.b R.Q ∧ (∀ i,(R.alloy.B.a.params i).supportExponent=100) ∧
      Tendsto R.Q atTop atTop ∧ Mallow.FrameAccord R.kit.target R.rolls R.alloy.delay ∧ ∃ Θ, ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v :=by
    let C:=b
    choose s hp using fun d:ℕ=> ((eventually_ge_atTop 1).and (A.B.a.fits.deep.eventually_ge_atTop (d+3))).exists
    have hb (d): 1 ≤ s d:= hp d|>.1
    obtain ⟨T,⟨Z⟩,hD⟩:= FullVolume.rodB X Φ
    let ht(d):d+3 ≤ (Issue.trail T).levels.clock.J (s d):= hp d|>.2
    have hZ:=Z.receipts
    choose B hB using fun N p m (hm : m < N)=> Boutique.taste h (F₀:=L) hZ (hD N p) hm
    let U (N p:ℕ):Branch X T.history N p 0 := ⟨T.choice,fun i _ hm=> hZ.samples h _ _ _ hm,fun m _ he=> B N p m he⟩ -- dots need explicit
    obtain ⟨V,hC,hY,H⟩:= Bandage.coming h b hZ s ht U; let R : Run G:= ⟨M,P,A,X,Y,K,b,q,hU.ahead,T,Z,s,ht,ease U,V,hC,fun N m p hx=> Boutique.mountain T (B N p m hx),hY⟩
    let T':Campaign R:= ⟨c,τ,u,t,L,Φ,hD⟩
    exact ⟨R,T',hPrediction,purchased,rfl,⟨hP,he⟩,hy,⟨hb,U,rfl,fun N p m hm=> hB N p m hm,H⟩,rfl,hQ,hBa,hU,h100,hQs,hYf,θ1,hcR,⟨hv,hψ,hν,hΩ,hPγ,hG⟩⟩

end
end YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint

