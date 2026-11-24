import YM.Integration.WilsonIndependentMatchedRosterPool
import YM.Integration.WilsonOriginalPublicPlantedJoinedCensus

/-! All ordinary subfaces of a comparable reflected roster, all signed slots
and all lower/survey choices use one actual canonical finite course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterCourse
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
    (phase:4  ≤  j)
variable {I:Type}(P:Run G)(W:Initialize G)(kind:I→Bool)(d:I→ℕ){h D k u₀:ℕ}
    (cap:∀ i,d i  ≤  h)(p:h<D)(native:∀ i,d i  ≤  k)(v:Rails h k u₀ e)
local notation "C" => Credit.leanC
local notation "Cuts" => CutsP H (R.T h) p v C C C C
local notation "src" i:arg => WilsonIndependentMatchedNamedPair.sectionAt P W (kind i) (d i)
local notation "col" i:arg => WilsonIndependentMatchedFiledIncome.plate (src i) ((cap i).trans_lt p)

open WilsonIndependentEvenPassport (count)
open WilsonIndependentMatchedCensusReceipt (Filed Pair Axis)

open WilsonIndependentMatchedRosterPool (Billed)
include native premium in
theorem original (covered:h ≤ height)(dim:D ≤ seats)(input:k ≤ seats)(test:u₀ ≤ seats)
    (τ u b:ℕ)(room:u+b ≤ u₀)(join:τ*k ≤ b)(output:b ≤ seats)
    (gap:1 ≤ (b:ℝ)-((τ*h:ℕ):ℝ)-(τ:ℝ)/4)(η:ℝ)(positive:0<η):
    ∃ α:(i:I)→Alma (P.family.labels.level (d i))→ℝ,(∀i a,0  ≤  α i a) ∧ ∀ᶠ idx:ℕ in atTop,
      ∀i:Requests B.a,i.val=idx →
      let δ:=(V.step i.val).spacing
      let amp:=fun n:I=>δ^(h-d n)
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let N:=count V B.a i.val
      ∃(A:Levels G)(s:ℕ),A.clock.kernel=kernel ∧
        (∀f:RegulatorIR.Ledger.Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i →
          ∀per:ℕ,(A.clock.op (s+(N-(f.offset+1))) per).patch=cir.pactP f) ∧
      ∃L:Torch H (R.T h) p v C C C,L.L.V.draws=A ∧ L.L.V.paid=chart ∧ L.L.V.anchor=s ∧
        (∀j ≤ old V B.a idx,L.L.V.y (s+j) ≤ B.cap) ∧
        (∀k' u' lag:ℕ,k'+lag ≤ seats→u' ≤ seats→Dormitory L.L.V k' u' C ∧ SpringD L.L.V k' u' (k'+lag) C) ∧
        ∀c:(n:I)→Verse (P.family.labels.level (d n)),∃X:I→Cuts,
        (∀n:I,Filed (X n) L V B.a i.val s (amp n) δ η
          (WilsonIndependentMatchedFiledIncome.charge e (c n) (α n)) (Shrine (col n) (c n))) ∧
        ∀(g:Fin τ)(slot:Fin (g.val+1)→I)(flag:Fin (g.val+1)→Bool)
          (a B':Fin (g.val+1)→ℝ)(peers:Fin (g.val+1)→Verse (R.F h))
          (φ:Fin (g.val+1)→Rarity D)(y t z:ℝ)(o:CellR),0<t→
          (∀v w,v≠w→ClearDay (φ v) (φ w) t)→(∀s,radiusH (φ s) 1 y ≤ z)→(∀s,Amplitude (φ s) (B' s))→
          Billed V B.a idx flag u b η (fun s=>X (slot s)) s φ a (fun s=>amp (slot s))
            (fun s=>WilsonIndependentMatchedFiledIncome.charge e (c (slot s)) (α (slot s))) B' peers y t z o:=by
  have B₀:0 ≤ B.cap:=(by linarith [(B.limits ⟨0,B.positive⟩).1,(B.limits ⟨0,B.positive⟩).2]
      :0 ≤ B.cap)
  obtain ⟨α,apos,census⟩:=WilsonOriginalPublicPlantedJoinedCensus.original R chart kernel V B premium phase
    P W kind d cap p native v covered dim input test η positive
  refine ⟨α,apos,?_⟩
  filter_upwards [census,WilsonIndependentMatchedRosterPool.original (H:=H) (T:=R.T h) (p:=p) (v:=v)
      (E:=C) (W:=C) (K:=C) (U:=C) V B.a τ u b C C B.cap η B₀ positive room join v.hk gap]
    with idx appointed gate i same δ amp cir N
  subst idx
  obtain ⟨A,s,ker,patch,L,L',identity,draw,clock,source,ages,fees,program⟩:=appointed i rfl
  have apportioned (j:ℕ)(hj:j ≤ old V B.a i.val):L.L.V.y (s+j) ≤ B.cap:=ages j
    (hj.trans (Nat.le_add_right _ _))
  refine ⟨A,s,ker,patch,L,draw,clock,source,apportioned,fees,?_⟩
  intro c
  obtain ⟨X,rows,_⟩:=program c
  have salary (n:I): Filed (X n) L V B.a i.val s (amp n) δ η
      (WilsonIndependentMatchedFiledIncome.charge e (c n) (α n)) (Shrine (col n) (c n)):=by
    obtain ⟨school,report,top,time,word,rent,net,scale,_⟩:=rows n
    exact WilsonIndependentMatchedCensusReceipt.placed (X n) L V B.a i.val s (amp n) δ η _ _
      (pow_pos (V.step i.val).positive _) school report top time word rent net scale
  refine ⟨X,salary,?_⟩
  intro g slot flag a B' peers φ y t z o ht sep rad bill
  have hu:u ≤ seats:=(Nat.le_add_right u b).trans (room.trans test)
  have rank:WilsonIndependentMatchedRosterCuts.ranks flag k h ≤ (g.val+1)*k:=by
    have point(s:Fin (g.val+1)):WilsonIndependentMatchedRosterSlots.degree (flag s) k h ≤ k:=by
      cases flag s <;> simp [WilsonIndependentMatchedRosterSlots.degree,v.hk]
    simpa [WilsonIndependentMatchedRosterCuts.ranks] using Finset.sum_le_sum (s:=Finset.univ) (fun s _=>point s)
  have full:WilsonIndependentMatchedRosterCuts.ranks flag k h ≤ seats:=
    rank.trans ((Nat.mul_le_mul_right k g.isLt).trans (join.trans output))
  exact gate g flag L _ s φ a _ _ B' peers _ y t z o (fun j=>salary (slot j)) apportioned source
    (fees b u 0 (by omega) hu).2 (fees _ u 0 (by omega) hu).1 ht sep rad
    (fun s=>Finset.sum_nonneg (fun j _=>WilsonIndependentMatchedFiledIncome.nonneg (apos _ j) _ e)) bill

end YM.Integration.WilsonIndependentMatchedRosterCourse
