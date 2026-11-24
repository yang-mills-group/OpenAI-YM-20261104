import YM.Integration.WilsonCoherentMayerColumn
import YM.Integration.WilsonMeasuredSupportWindow
import YM.Integration.WilsonCoherentMayerPortfolio
import YM.Integration.WilsonCoherentMayerSignedCharge

/-! The original forecast selects one captain before all nonzero physical components and submitted stencils. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerSurvivor
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat.Legato WilsonCoherentMayerGate WilsonCoherentMayerSubmission
open WilsonCoherentMayerSignedCharge (polynomial residual)
open LocalLTE.Fan
variable {G:Gauge} {c f L:Side}{S:StepData c f}{T:Tube G S}{R:Rep G f}
    {P:Teller G}{Q:ConnectedActivityE6.Target G P}{W s μ C:ℝ}{o:Target.Order G W}
    (run:Run G) {I:Type} [Fintype I] (d:I→ℕ) (H:Cash W s μ L Q o C T R)
    (M taylor:ℕ) (share:ℝ)

def Returned (fare:Head S→ℝ) (θ:ℝ):Prop:=
  ∀ (entry:Submitted run R I), d=entry.grade→(∀i z,|entry.phase i z|≤‖z‖)→
  ∀(old:Team R)(fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn) (loc:H.ThinP)
    (veil:Finset (Veil c f)) (q:ℕ), MeasuredSupport.Component H loc veil q →
    (together entry old fresh).signs S⊆loc.val → ∀ grade:Orders M,grade.val≤M →
    let entered:=together entry old fresh
    |Laminate.column entered loc.val H (χ:=Chi.canonical) M grade 1-
       WilsonCoherentMayerColumn.model (χ:=Chi.canonical) (M:=M) run entry old fresh taylor loc grade.val| ≤
      (old.weight*(∏i∈loc.val\entered.signs S,fare i)*Mayer.spreadRate M θ 1^loc.val.card)*
      (WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label*share)

def Issued (j:ℕ):Prop:=
  ∃ (A a' C' d' v t r B q e K θ uJ vJ:ℝ) (k l:ℕ) (N:Captain H j C' d' v t A a' r B q (l+j) Chi.canonical),
    Q.goal L s≤K ∧ Mayer.Approved K θ j M ∧ Awning H N.conduit A a'
       (betaF G s L ^ (-(↑(M+1:ℕ)):ℝ)) e uJ vJ k l ∧
    Returned run d H M taylor share N.conduit.fare θ

theorem purchased {a w cost η:ℝ} {j distance:ℕ} (funded:Laminate.Known H a w cost η j distance M)
    {Ctable:ℝ} (non:0≤Ctable) (paid:WilsonCoherentMayerOnCourse.At run d H taylor Ctable)
    (price:Ctable*(Coat.gStep R.beta)^(taylor+1) ≤ share):
    Issued run d H M taylor share j:=by
  obtain ⟨A,a',C',d',v,t,r,B,q,e,K,θ,uJ,vJ,k,l,N,room,allow,law,_,_⟩:=funded
  refine ⟨A,a',C',d',v,t,r,B,q,e,K,θ,uJ,vJ,k,l,N,room,allow,law,?_⟩
  intro entry same contract old fresh loc veil height stage coverage grade live
  subst d
  have start:Mayer.Start loc.val:=by
    rw [stage.lift]
    intro i hi
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hi
    exact ⟨LocalLTE.Fan.chapter v,rfl⟩
  have shape:roster loc.val=(⟨∅,∅,∅⟩:Stores S):=stage.lift ▸ LocalLTE.Fan.Field.rosterD _
  have measured:=WilsonCoherentMayerColumn.submitted run entry old fresh taylor loc N law room allow contract paid coverage
    start ⟨stage.burns,stage.players⟩ shape (SectorMeasure.temp_nonneg _) H.laws.intake.positive grade live non
  let p:=loc.val\(together entry old fresh).signs S
  have ow:0≤old.weight:=Finset.prod_nonneg (fun x _=>x.profit)
  have nf:0≤∏i∈p,N.conduit.fare i:=Finset.prod_nonneg (fun i _=>N.conduit.fares i)
  have spread:0≤Mayer.spreadRate M θ 1:=zero_le_one.trans (Mayer.spread_pos le_rfl allow.nonneg)
  have cash:=mul_nonneg (mul_nonneg ow nf) (pow_nonneg spread loc.val.card)
  have mn:0≤WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label:=
    Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  exact measured.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left price mn) cash)

end YM.Integration.WilsonCoherentMayerSurvivor
