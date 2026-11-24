import YM.Integration.WilsonIndependentMatchedRosterBasis
import YM.Integration.WilsonIndependentMatchedRosterObserved

/-! The complete fitted reading and the independently normalized basis
hearings below it share the same posted physical source and actual clock. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterBundle
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
    (phase:4   ≤   j)
variable {I:Type}(P:Run G)(W:Initialize G)(kind:I→Bool)(d:I→ℕ){h D k u₀:ℕ}
    (cap:∀ i,d i   ≤   h)(p:h<D)(native:∀ i,d i   ≤   k)(v:Rails h k u₀ e)
local notation "C" => Credit.leanC
local notation "Cuts" => CutsP H (R.T h) p v C C C C
local notation "src" i:arg => WilsonIndependentMatchedNamedPair.sectionAt P W (kind i) (d i)
local notation "col" i:arg => WilsonIndependentMatchedFiledIncome.plate (src i) ((cap i).trans_lt p)

open WilsonIndependentEvenPassport (count)
open WilsonIndependentMatchedCensusReceipt (Filed Pair Axis)

open WilsonIndependentMatchedRosterPool (Billed)
open WilsonIndependentMatchedRosterSlots (degree)
open WilsonIndependentMatchedRosterCuts (ranks counts)
open WilsonIndependentMatchedRosterStop (Hearing)
open WilsonIndependentMatchedRosterChronology (mass)
open WilsonIndependentMatchedPivotSeat (axis)
open WilsonIndependentMatchedRosterReception (perSite)
open WilsonIndependentMatchedRosterWages (geo)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedRosterMasks (quiet choose)
open WilsonIndependentMatchedRosterPlanted (response toll)

include native premium in
theorem original (covered:h  ≤  height)(dim:D  ≤  seats)(input:k  ≤  seats)(test:u₀  ≤  seats)
    (τ u b:ℕ)(room:u+b  ≤  u₀)(join:τ*k  ≤  b)(output:b  ≤  seats)
    (gap:1  ≤  (b:ℝ)-((τ*h:ℕ):ℝ)-(τ:ℝ)/4)(η:ℝ)(positive:0<η):
    ∃ α:(i:I)→Alma (P.family.labels.level (d i))→ℝ,(∀i a,0   ≤   α i a) ∧ ∀ᶠ idx:ℕ in atTop,
      ∀i:Requests B.a,i.val=idx →
      let δ:=(V.step i.val).spacing
      let amp:=fun n:I=>δ^(h-d n)
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let N:=count V B.a i.val
      ∃(A:Levels G)(s:ℕ),A.clock.kernel=kernel ∧
        (∀f:RegulatorIR.Ledger.Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i →
          ∀per:ℕ,(A.clock.op (s+(N-(f.offset+1))) per).patch=cir.pactP f) ∧
      ∃L:Torch H (R.T h) p v C C C,L.L.V.draws=A ∧ L.L.V.paid=chart ∧ L.L.V.anchor=s ∧
        (∀j  ≤  old V B.a idx,L.L.V.y (s+j)  ≤  B.cap) ∧
        (∀k' u' lag:ℕ,k'+lag  ≤  seats→u'  ≤  seats→Dormitory L.L.V k' u' C ∧ SpringD L.L.V k' u' (k'+lag) C) ∧
        ∀c:(n:I)→Verse (P.family.labels.level (d n)),∃X:I→Cuts,
        (∀n:I,Filed (X n) L V B.a i.val s (amp n) δ η
          (WilsonIndependentMatchedFiledIncome.charge e (c n) (α n)) (Shrine (col n) (c n))) ∧
        (∀(g:Fin τ)(slot:Fin (g.val+1)→I)(a B':Fin (g.val+1)→ℝ)(φ:Fin (g.val+1)→Rarity D)
          (y t z:ℝ)(o:CellR),0<t→(∀a b,a≠b→ClearDay (φ a) (φ b) t)→
          (∀s,radiusH (φ s) 1 y ≤ z)→(∀s,Amplitude (φ s) (B' s))→∀stop ≤ old V B.a idx,
          let Y:=fun s=>X (slot s)
          let mesh:=fun s=>paceT (Y s).ax.S (Y s).m ((Y s).m+(Y s).i)
          let planted:=fun s=>word (a s • Shrine (col (slot s)) (c (slot s))) (φ s) (mesh s) y o h
          let fitted:=fun s=>receiving (Y s) (a s/amp (slot s)) (φ s) y o (Y s).i
          let read:=cruises (Y 0).ax (Y 0).tx (Y 0).N ((g.val+1)*k) ((Y 0).m+(Y 0).i) (s+stop)
          response e u (read (MassP G ℝ g.val planted)-read (MassP G ℝ g.val fitted))
            (∑j∈Finset.univ.erase (quiet g.val),toll Y (choose g.val j) b u δ η t z a (fun s=>amp (slot s))
              (fun s=>WilsonIndependentMatchedFiledIncome.charge e (c (slot s)) (α (slot s))) B')) ∧
        (∀(g:Fin τ)(slot:Fin (g.val+1)→I)(flag:Fin (g.val+1)→Bool)
          (a B':Fin (g.val+1)→ℝ)(name:Fin (g.val+1)→Alma (R.F h))(q:Fin (g.val+1)→ℕ)
          (φ:Fin (g.val+1)→Rarity D)(y t z:ℝ)(o:CellR),(∀s,q s ≤ e)→0<t→0 ≤ z→(∀s,0 ≤ B' s)→
          (∀v w,v≠w→ClearDay (φ v) (φ w) t)→(∀s,radiusH (φ s) 1 y ≤ z)→(∀s,Amplitude (φ s) (B' s))→
          let Y:=fun s=>X (slot s)
          let rent:=fun s=>WilsonIndependentMatchedFiledIncome.charge e (c (slot s)) (α (slot s))
          let M:=fun s=>WilsonIndependentMatchedRosterAxes.source (flag s) (a s) (rent s)
          let fields:=fun s=>WilsonIndependentMatchedRosterSlots.entry (flag s) (Y s) (a s/amp (slot s))
            (axis (name s) (q s)) (φ s) y o
          ∀stop ≤ old V B.a idx,Hearing (Y 0) (ranks flag k h) u ((Y 0).m+(Y 0).i) (s+stop) (mass fields (Y 0).i)
            (geo g.val e u b (fun s=>degree (flag s) k h) t z*perSite u b z M B'*
             δ^((counts flag:ℝ)/4-((g.val+3:ℕ):ℝ)*η))):=by
  obtain ⟨α,apos,program⟩:=WilsonIndependentMatchedRosterCourse.original R chart kernel V B premium phase P W kind d cap p native v
    covered dim input test τ u b room join output gap η positive
  refine ⟨α,apos,?_⟩
  filter_upwards [program,WilsonIndependentMatchedRosterAxes.original (H:=H) (T:=R.T h) (p:=p) (v:=v)
    (E:=C) (W:=C) (K:=C) (U:=C) V B.a u b B.cap η positive] with idx grant funded i same δ amp cir N
  obtain ⟨A,s,ker,patch,L,draw,rat,anchor,ages,fees,files⟩:=grant i same
  refine ⟨A,s,ker,patch,L,draw,rat,anchor,ages,fees,?_⟩
  intro c
  obtain ⟨X,filed,hear⟩:=files c
  refine ⟨X,filed,?_,?_⟩
  · intro g slot a B₁ φ y t z o ht sep radius amps stop older
    subst idx
    exact WilsonIndependentMatchedRosterPlanted.original V B.a i.val s u b L (fun v=>X (slot v)) φ a (fun v=>amp (slot v)) _
      B₁ (fun v=>Shrine (col (slot v)) (c (slot v))) y t z η o amps (fun v=>filed (slot v))
      (fun flag=>hear g slot flag a B₁ _ φ y t z o ht sep radius amps) stop older
  · intro g slot flag a B₁ name q φ y t z o grade ht hz hB sep radius amps
    subst idx
    exact funded g.val L (fun s=>X (slot s)) s φ flag a (fun s=>amp (slot s)) _ B₁ name q _
      y t z o (fun s=>filed (slot s)) ages grade ht hz
      (fun s=>Finset.sum_nonneg (fun j _=>WilsonIndependentMatchedFiledIncome.nonneg (apos _ j) _ e)) hB
      (hear g slot flag a B₁ _ φ y t z o ht sep radius amps)

end YM.Integration.WilsonIndependentMatchedRosterBundle
