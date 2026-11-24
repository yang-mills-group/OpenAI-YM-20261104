import YM.Integration.WilsonIndependentMatchedInheritedLibrary
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
namespace YM.Integration.WilsonIndependentMatchedInheritedCensus
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

open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMatchedRosterMasks (choose quiet)
open WilsonIndependentMatchedRosterCuts (ranks)
open WilsonIndependentMatchedRosterPlanted (toll)
open WilsonIndependentMatchedInheritedComparison (heard refund wage)
open private rooms from YM.Integration.WilsonIndependentMatchedRosterPool

local notation "Qₛ" n:arg => fun _:Fin (n+1)=>sectionSeal (R.T h) p

include native premium in
theorem original (covered:h ≤ height)(dim:D ≤ seats)(input:k ≤ seats)(test:u ≤ seats)
    (τ u₁ b:ℕ)(width:u₁+b ≤ u)(stage:τ*k ≤ b)(budget:b ≤ seats)
    (retained:τ*h+2 ≤ seats)(η:ℝ)(small:0<η)
    (spread:1 ≤ (b:ℝ)-((τ*h:ℕ):ℝ)-(τ:ℝ)/4):
    ∃(α:(i:I)→Alma (P.family.labels.level (d i))→ℝ)(credit wallet:Fin τ→Credit),
    (∀i a,0 ≤ α i a) ∧ ∀ᶠ idx:ℕ in atTop,∀i:Requests B.a,i.val=idx →
      let δ:=(V.step i.val).spacing
      let amp:=fun l:I=>δ^(h-d l)
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let np:=WilsonIndependentEvenPassport.count V B.a i.val
      ∃(A:Levels G)(s:ℕ),A.clock.kernel=kernel ∧
        (∀ f:RegulatorIR.Ledger.Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i →
          ∀ per:ℕ,(A.clock.op (s+(np-(f.offset+1))) per).patch=cir.pactP f) ∧
      ∃L:Torch H (R.T h) p v C C C,L.L.V.draws=A ∧ L.L.V.paid=chart ∧ L.L.V.anchor=s ∧
        ∀N:ℕ,s+np ≤ N → ∀c:(l:I)→Verse (P.family.labels.level (d l)),∃X:I→Cuts,
        let fees:=fun t:I=>WilsonIndependentMatchedFiledIncome.charge e (c t) (α t)
        let stem:=fun t:I=>Shrine (col t) (c t)
        (∀t,(X t).pt=amp t • stem t ∧
          Recorded (X t) L V B.a i.val s N (amp t) δ η (fees t) (stem t)) ∧
        ∀(g:Fin τ)(slot:Fin (g.val+1)→I)(a B₁:Fin (g.val+1)→ℝ)(φ:Fin (g.val+1)→Rarity D)(y t z:ℝ)(o:CellR),
        0<t → (∀l l',l≠l' → ClearDay (φ l) (φ l') t) → (∀l,radiusH (φ l) 1 y ≤ z) →
        (∀l,Amplitude (φ l) (B₁ l)) → ∀stop ≤ old V B.a i.val,∀(Z:ℝ)(upper N':ℕ),
        s+np ≤ upper → upper ≤ N → upper ≤ N' →
        Compar A.S L.L.V.y (s+stop) (s+old V B.a i.val) ≤ Z → Bough (Qₛ g.val) φ y Z B₁ →
        ∀r ≤ e,∀x:Fin 0→YForest G,
          ‖(heard (X∘slot) a φ (stem∘slot) (s+stop) y o).2 r 0 x-
            (refund (X∘slot) a (amp∘slot) φ N' (s+stop) y o).2 r 0 x‖ ≤
          (∑l∈Finset.univ.erase (quiet g.val),toll (X∘slot) (choose g.val l) b u₁ δ η t z a (amp∘slot) (fees∘slot) B₁)+
          wage (X∘slot) a (amp∘slot) B₁ (credit g) (wallet g) ((X (slot 0)).vesselsC.y) Z upper:=by
  have cap₀:0 ≤ B.cap:=by linarith [(B.limits ⟨0,B.positive⟩).1,(B.limits ⟨0,B.positive⟩).2]
  have smaller:u₁ ≤ seats:=((Nat.le_add_right u₁ b).trans width).trans test
  obtain ⟨α,nn,book⟩:=WilsonIndependentMatchedInheritedLibrary.original R chart kernel V B premium phase P W
    kind d cap p native v covered dim input test
  have widths (g:Fin τ):(g.val+1)*k ≤ b:=(Nat.mul_le_mul_right _ g.isLt).trans stage
  have spreads (g:Fin τ):1 ≤ (b:ℝ)-(((g.val+1)*h:ℕ):ℝ)-((g.val+1:ℕ):ℝ)/4:=by
    have h₁:(((g.val+1)*h:ℕ):ℝ) ≤ ((τ*h:ℕ):ℝ):=by exact_mod_cast (Nat.mul_le_mul_right h g.isLt)
    have h₂:((g.val+1:ℕ):ℝ) ≤ (τ:ℝ):=by exact_mod_cast g.isLt
    linarith
  choose credit wallet heard using fun g:Fin τ=>WilsonIndependentMatchedInheritedHearing.original
    (n:=g.val) (H:=H) (T:=R.T h) (p:=p) (v:=v) (E:=C) (W:=C) (U:=C) (V:=C)
    V B.a u₁ b C C C C B.cap η cap₀ small width (widths g) (spreads g)
  refine ⟨α,credit,wallet,nn,?_⟩
  filter_upwards [Filter.eventually_all.mpr heard] with idx pay i same δ amp cir np
  subst idx
  obtain ⟨A,s,ker,patches,L,draw,chart',anchor,tariff,rates,frames,inlet⟩:=book i
  refine ⟨A,s,ker,patches,L,draw,chart',anchor,?_⟩
  intro N fine c
  obtain ⟨X,got⟩:=inlet N fine c
  refine ⟨X,fun t=>⟨(got t).1,(got t).2.2 η⟩,?_⟩
  intro g slot a B₁ φ y t z o ht sep radii tests stop whereAt Z upper N' buffer fine' other room shape
  let rent:=fun s=>WilsonIndependentMatchedFiledIncome.charge e (c (slot s)) (α (slot s))
  let stems:=fun s=>Shrine (col (slot s)) (c (slot s))
  have names:=WilsonIndependentCutJoinNativeFrames.roster frames (Qₛ g.val)
    (fun _=>⟨covered,dim,rfl⟩)
  have sectors (flag:Fin (g.val+1)→Bool):Dormitory L.L.V (ranks flag k h) u₁ C:=
    (rates _ u₁ 0 (by simpa using ((rooms flag g.isLt v.hk stage spread).1.trans budget)) smaller).1
  have smallCap:capP (Qₛ g.val)+2 ≤ seats:=by
    simpa [capP,asp,sectionSeal] using (Nat.add_le_add_right (Nat.mul_le_mul_right h g.isLt) 2).trans retained
  have shapeCharge (s):0 ≤ rent s:=
    Finset.sum_nonneg (fun f _=>WilsonIndependentMatchedFiledIncome.nonneg (nn (slot s) f) _ e)
  have file (v:Fin (g.val+1)):= (got (slot v)).2.2 η
  have first:(X (slot 0)).vesselsC=L.L.V:=congrArg (fun a=>a.L.V) (file 0).school
  have K':(X (slot 0)).ceilC=s+np:=by
    change (X (slot 0)).m+(X (slot 0)).i=_
    rw [(file 0).report,(file 0).gap]
    dsimp only [np,WilsonIndependentEvenPassport.count];omega
  exact pay g L (X∘slot) s N φ a (amp∘slot) rent B₁ stems y t z o file
    (fun l hl=>tariff l (hl.trans (Nat.le_add_right _ _))) anchor (rates b u₁ 0 (by simpa using budget) smaller).2
    sectors names.1 (rates _ u₁ 2 smallCap smaller).2 (rates _ u₁ 2 smallCap smaller).1 ht sep radii shapeCharge tests
    stop whereAt Z upper N' (K' ▸ buffer) fine' other (by
      change Compar (X (slot 0)).vesselsC.draws.S (X (slot 0)).vesselsC.y _ (X (slot 0)).m ≤ _
      rwa [first,draw,(file 0).report]) shape
end YM.Integration.WilsonIndependentMatchedInheritedCensus
