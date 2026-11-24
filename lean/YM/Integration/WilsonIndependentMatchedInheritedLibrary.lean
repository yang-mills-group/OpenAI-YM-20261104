import YM.Integration.WilsonOriginalPublicPlantedJoinedCensus
import YM.Integration.WilsonIndependentMatchedInheritedHearing
import YM.Integration.WilsonIndependentCutJoinNativeFrames
import YM.Integration.WilsonIndependentCutJoinGrant
import YM.Integration.WilsonIndependentMatchedCoverDouble

/-! The complete fitted census and the larger rank of its normalized product
are paid on one auxiliary Wilson history before any of the doses or tests.
The reporting scale is in the same physical units as the submitted sources. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedInheritedLibrary
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open WilsonIndependentEvenPassport (old young)
open WilsonIndependentExactPlate (Requests)
open WilsonOriginalPublicPlantedStableCredit (span)
open WilsonIndependentMatchedCoveredSeats (Posted seat)
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}(R:Master H)(chart:ChartRatio G)(kernel:KernelChoices)
    (V:XSpace.Run){j e height seats extra:ℕ}
    (B:WilsonIndependentEvenPassport.Menu R chart kernel V e height seats j extra)
    (premium:WilsonIndependentCutJoinPlate.Approved R chart kernel V e height seats j extra B)
    (phase:4 ≤ j)
variable {I:Type}(P:Run G)(W:Initialize G)(kind:I→Bool)(d:I→ℕ){h D k u:ℕ}
    (cap:∀ i,d i ≤ h)(p:h<D)(native:∀ i,d i ≤ k)(v:Rails h k u e)
local notation "C" => Credit.leanC
local notation "Cuts" => CutsP H (R.T h) p v C C C C
local notation "src" i:arg => WilsonIndependentMatchedNamedPair.sectionAt P W (kind i) (d i)
local notation "col" i:arg => WilsonIndependentMatchedFiledIncome.plate (src i) ((cap i).trans_lt p)

open WilsonIndependentMatchedInheritedCuts (Recorded)
open WilsonIndependentCutJoinNativeFrames (Funded)
open WilsonIndependentEvenPassport (count)

include native premium in
theorem original (covered:h ≤ height)(dim:D ≤ seats)(input:k ≤ seats)(test:u ≤ seats):
    ∃α:(i:I)→Alma (P.family.labels.level (d i))→ℝ,(∀i a,0 ≤ α i a) ∧
    ∀i:Requests B.a,
      let δ:=(V.step i.val).spacing
      let amp:=fun b:I=>δ^(h-d b)
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let np:=WilsonIndependentEvenPassport.count V B.a i.val
      ∃(A:Levels G)(s:ℕ),A.clock.kernel=kernel ∧
        (∀ f:RegulatorIR.Ledger.Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i →
          ∀ per:ℕ,(A.clock.op (s+(np-(f.offset+1))) per).patch=cir.pactP f) ∧
      ∃(L:Torch H (R.T h) p v C C C),L.L.V.draws=A ∧ L.L.V.paid=chart ∧ L.L.V.anchor=s ∧
        (∀ t ≤ np,L.L.V.y (s+t) ≤ B.cap) ∧
        (∀ rank moment lag:ℕ,rank+lag ≤ seats → moment ≤ seats →
          Dormitory L.L.V rank moment C ∧ SpringD L.L.V rank moment (rank+lag) C) ∧
        Funded R L.L.V height seats ∧
        ∀N:ℕ,s+np ≤ N → ∀c:(b:I)→Verse (P.family.labels.level (d b)),∃X:I→Cuts,
        ∀b:I,(X b).pt=amp b • Shrine (col b) (c b) ∧
          (X b).fuel=amp b*WilsonIndependentMatchedFiledIncome.charge e (c b) (α b) ∧
          ∀η:ℝ,Recorded (X b) L V B.a i.val s N (amp b) δ η
            (WilsonIndependentMatchedFiledIncome.charge e (c b) (α b)) (Shrine (col b) (c b)):=by
  choose α nn admitted using fun b:I=>WilsonIndependentMatchedFiledIncome.named P W (kind b)
    (d b) ((cap b).trans_lt p) (native b) e u
  refine ⟨α,nn,?_⟩
  intro i δ amp cir np
  obtain ⟨A,s,ker,_,path,geometry,home,hall⟩:=WilsonIndependentCutJoinPlate.optics
    R chart kernel V e height seats j extra B premium phase i
  obtain ⟨L',draw,clock,price,root,_,_,torches,bill⟩:=hall h D p covered dim
  obtain ⟨L,ident⟩:=torches k u v input test
  have paid (t:ℕ)(ht:t ≤ np): L.L.V.y (s+t) ≤ B.cap:=by
    rw [ident,price,home t ht]
    exact (B.limits _).2
  have more:=WilsonIndependentCutJoinNativeFrames.original R A chart _ s hall L.L.V
    (ident ▸ draw) (ident ▸ clock) (ident ▸ price) (ident ▸ root)
  refine ⟨A,s,ker,path,L,ident ▸ draw,ident ▸ clock,ident ▸ root,paid,ident ▸ bill,more,?_⟩
  intro N fine c
  let m:=s+old V B.a i.val
  let n:=young B.a i.val
  have fixed:m+n=s+np:=by dsimp only [m,n,np,WilsonIndependentEvenPassport.count];omega
  have live:L.L.V.anchor ≤ m:=by rw [ident,root];exact Nat.le_add_right ..
  let fee b:=WilsonIndependentMatchedFiledIncome.charge e (c b) (α b)
  have hp (b:I):0<amp b:=pow_pos (V.step i.val).positive _
  let X (b:I):Cuts:=WilsonIndependentMatchedKernelResidual.diagonal L L' ident.symm m n N live
    (fixed ▸ fine) (amp b • Shrine (col b) (c b)) ((admitted b (c b)).1.μ (amp b)) (amp b*fee b)
    (mul_nonneg (hp b).le (admitted b (c b)).2.1) (by
      intro lag r hl
      have row:=((admitted b (c b)).2.2 lag r hl).μ (amp b)
      rwa [abs_of_pos (hp b)] at row)
  refine ⟨X,fun b=>⟨rfl,rfl,?_⟩⟩
  intro η
  apply WilsonIndependentMatchedInheritedCuts.placed (X b) L V B.a i.val s N (amp b) δ η
    (fee b) (Shrine (col b) (c b)) (hp b) rfl rfl rfl rfl rfl rfl (X b).carve1
  change L.L.V.draws.S.scale (m+n)-L.L.V.draws.S.scale m=_
  rw [ident,draw,fixed]
  exact geometry

end YM.Integration.WilsonIndependentMatchedInheritedLibrary
