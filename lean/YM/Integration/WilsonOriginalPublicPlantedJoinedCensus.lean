import YM.Integration.WilsonOriginalPublicPlantedGroupedReturn
import YM.Integration.WilsonIndependentCutJoinGrant
import YM.Integration.WilsonIndependentMatchedCoverDouble

/-! The complete fitted census and the larger rank of its normalized product
are paid on one auxiliary Wilson history before any of the doses or tests.
The reporting scale is in the same physical units as the submitted sources. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPlantedJoinedCensus
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

include native premium in
theorem original (covered:h ≤ height)(dim:D ≤ seats)(input:k ≤ seats)(test:u ≤ seats)
    (θ:ℝ)(positive:0<θ):
    ∃ α:(i:I)→Alma (P.family.labels.level (d i))→ℝ,(∀i a,0 ≤ α i a) ∧ ∀ᶠ idx:ℕ in atTop,
      ∀i:Requests B.a,i.val=idx →
      let δ:=(V.step i.val).spacing
      let amp:=fun b:I=>δ^(h-d b)
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let N:=WilsonIndependentEvenPassport.count V B.a i.val
      ∃(A:Levels G)(s:ℕ),A.clock.kernel=kernel ∧
        (∀ f:RegulatorIR.Ledger.Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i →
          ∀ per:ℕ,(A.clock.op (s+(N-(f.offset+1))) per).patch=cir.pactP f) ∧
      ∃(L:Torch H (R.T h) p v C C C)(L':ChorusLine H (R.T h) p e C C C),
        L.L=L'.arch ∧ L.L.V.draws=A ∧ L.L.V.paid=chart ∧
        L.L.V.anchor=s ∧
        (∀ t ≤ N,L.L.V.y (s+t) ≤ B.cap) ∧
        (∀ rank moment lag:ℕ,rank+lag ≤ seats → moment ≤ seats →
          Dormitory L.L.V rank moment C ∧ SpringD L.L.V rank moment (rank+lag) C) ∧
        ∀c:(b:I)→Verse (P.family.labels.level (d b)),∃X:I→Cuts,
        (∀b:I,let Y:=X b
          let fee:=WilsonIndependentMatchedFiledIncome.charge e (c b) (α b)
          Y.L=L ∧ Y.m=s+old V B.a i.val ∧ Y.N=s+N ∧ Y.i=young B.a i.val ∧
          Y.pt=amp b • Shrine (col b) (c b) ∧ Y.fuel=amp b*fee ∧
          Y.springP Y.i=amp b • Shrine (col b) (c b)-Shrine Y.Ntop Y.tileP ∧
          span Y Y.i= -Real.log δ ∧
          ∀ lag ≤ e,∀ z ≤ Y.i,∀ r:ℕ,∀ moment ≤ u,
            Fruit 0 1 moment (((amp b)⁻¹ • Y.springP z).2 lag r)
              (δ^(-θ)*(δ/Real.exp (-span Y z))^(1/4:ℝ)*fee)) ∧
        (∀ b b':I,∀ φ ψ:Rarity D,∀ y:ℝ,∀ o:CellR,
          Posted (X b).vesselsC k k (X b).m (X b).N (X b).i
            (seat (X b) (amp b)⁻¹ φ y o) (seat (X b') (amp b')⁻¹ ψ y o)):=by
  choose α nn admitted using fun b:I=>WilsonIndependentMatchedFiledIncome.named P W (kind b)
    (d b) ((cap b).trans_lt p) (native b) e u
  refine ⟨α,nn,?_⟩
  filter_upwards [WilsonOriginalPublicPlantedStableCredit.original H (R.T h) p v C C C C V B.cap θ
     positive] with idx spend i same δ amp cir N
  subst idx
  obtain ⟨A,s,ker,_,path,geometry,home,hall⟩:=WilsonIndependentCutJoinPlate.optics
    R chart kernel V e height seats j extra B premium phase i
  obtain ⟨L',draw,clock,price,root,_,_,torches,bill⟩:=hall h D p covered dim
  obtain ⟨L,ident⟩:=torches k u v input test
  have paid (t:ℕ)(ht:t ≤ N): L.L.V.y (s+t) ≤ B.cap:=by
    rw [ident,price,home t ht]
    exact (B.limits _).2
  refine ⟨A,s,ker,path,L,L',ident,ident ▸ draw,ident ▸ clock,ident ▸ root,paid,ident ▸ bill,?_⟩
  intro c
  let m:=s+old V B.a i.val
  let n:=young B.a i.val
  have fixed:m+n=s+N:=by dsimp only [m,n,N,WilsonIndependentEvenPassport.count];omega
  have live:L.L.V.anchor ≤ m:=by rw [ident,root];exact Nat.le_add_right ..
  let fee b:=WilsonIndependentMatchedFiledIncome.charge e (c b) (α b)
  have hp (b:I):0<amp b:=pow_pos (V.step i.val).positive _
  let X (b:I):Cuts:=WilsonIndependentMatchedKernelResidual.diagonal L L' ident.symm m n (m+n) live le_rfl
    (amp b • Shrine (col b) (c b)) ((admitted b (c b)).1.μ (amp b)) (amp b*fee b)
    (mul_nonneg (hp b).le (admitted b (c b)).2.1) (by
      intro lag r hl
      have word:=((admitted b (c b)).2.2 lag r hl).μ (amp b)
      rwa [abs_of_pos (hp b)] at word)
  refine ⟨X,?_,?_⟩
  · intro b Y bill'
    have scale:span Y Y.i= -Real.log δ:=by
      change L.L.V.draws.S.scale (m+n)-L.L.V.draws.S.scale m=_
      rw [ident,draw,fixed]; exact geometry
    refine ⟨rfl,rfl,fixed,rfl,rfl,rfl,Y.carve1,scale,?_⟩
    have income:Y.vesselsC.y Y.m ≤ B.cap:=paid _ (by dsimp only [N,WilsonIndependentEvenPassport.count];omega)
    intro lag hl z hz r moment hm
    have got:=(spend Y income scale lag hl z hz r moment hm).μ (amp b)⁻¹
    have wage:abs ((amp b)⁻¹) *(δ^(-θ)*(δ/Real.exp (-span Y z))^(1/4:ℝ)*Y.fuel)=
       δ^(-θ)*(δ/Real.exp (-span Y z))^(1/4:ℝ)*bill':=by
      rw [abs_of_pos (inv_pos.mpr (hp b)),show Y.fuel=amp b*bill' from rfl]
      field_simp [(hp b).ne']
    rw [wage] at got
    exact got
  · intro b b' φ ψ y o
    exact WilsonIndependentMatchedCoveredSeats.joined (X b) (X b') rfl rfl rfl rfl _ _ φ ψ y o

end YM.Integration.WilsonOriginalPublicPlantedJoinedCensus
