import YM.Integration.WilsonIndependentMatchedRosterBundle
import YM.Integration.WilsonPositionThermometerGradedSource

/-! Each nonempty face of the prescribed (6,4,4) thermometer uses its
own literal sites on one dated torus and the common horizon-six output.
Unit-direction hears and the complete fitted difference share one bank. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterRose
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
abbrev grade (i:Fin 3):ℕ:=(WilsonPositionThermometerGradedSource.grade i).val
private lemma limit (i:Fin 3):grade i ≤ 6:=Nat.le_of_lt_succ (WilsonPositionThermometerGradedSource.grade i).isLt
def seatsFor (S:Finset (Fin 3))(live:S.Nonempty):Fin 3:=⟨S.card-1,by
  have h:S.card ≤ 3:=by simpa using Finset.card_le_univ S
  have :=Finset.card_pos.mpr live
  omega⟩
def address (S:Finset (Fin 3))(live:S.Nonempty):Fin ((seatsFor S live).val+1)↪o Fin 3:=
  S.orderEmbOfFin (by dsimp [seatsFor];have := Finset.card_pos.mpr live;omega)
lemma enrolled (S:Finset (Fin 3))(live:S.Nonempty):Set.range (address S live)=(S:Set (Fin 3)):=
  Finset.range_orderEmbOfFin _ _

variable {G:Gauge}{H:Hol G}(R:Master H)(chart:ChartRatio G)(kernel:KernelChoices)
    (V:XSpace.Run){j e height seats extra:ℕ}
    (B:WilsonIndependentEvenPassport.Menu R chart kernel V e height seats j extra)
    (premium:WilsonIndependentCutJoinPlate.Approved R chart kernel V e height seats j extra B)
    (phase:4    ≤    j)
variable (P:Run G)(W:Initialize G)(kind:Fin 3→Bool){D k u₀:ℕ}(p:6<D)(v:Rails 6 k u₀ e)
local notation "C" => Credit.leanC
local notation "Cuts" => CutsP H (R.T 6) p v C C C C
local notation "src" i:arg => WilsonIndependentMatchedNamedPair.sectionAt P W (kind i) (grade i)
local notation "col" i:arg => WilsonIndependentMatchedFiledIncome.plate (src i) ((limit i).trans_lt p)

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

include premium in
theorem original (covered:6 ≤ height)(dim:D ≤ seats)(input:k ≤ seats)(test:u₀ ≤ seats)
    (u b:ℕ)(room:u+b ≤ u₀)(join:3*k ≤ b)(output:b ≤ seats)(gap:1 ≤ (b:ℝ)-18-3/4)(η:ℝ)(positive:0<η):
    ∃ α:(i:Fin 3)→Alma (P.family.labels.level (grade i))→ℝ,(∀i a,0    ≤    α i a) ∧ ∀ᶠ idx:ℕ in atTop,
      ∀i:Requests B.a,i.val=idx →
      let δ:=(V.step i.val).spacing
      let amp:=fun n:Fin 3=>δ^(6-grade n)
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let N:=count V B.a i.val
      ∃(A:Levels G)(s:ℕ),A.clock.kernel=kernel ∧
        (∀f:RegulatorIR.Ledger.Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i →
          ∀per:ℕ,(A.clock.op (s+(N-(f.offset+1))) per).patch=cir.pactP f) ∧
      ∃L:Torch H (R.T 6) p v C C C,L.L.V.draws=A ∧ L.L.V.paid=chart ∧ L.L.V.anchor=s ∧
        (∀j   ≤   old V B.a idx,L.L.V.y (s+j)   ≤   B.cap) ∧
        (∀k' u' lag:ℕ,k'+lag   ≤   seats→u'   ≤   seats→Dormitory L.L.V k' u' C ∧ SpringD L.L.V k' u' (k'+lag) C) ∧
        ∀c:(n:Fin 3)→Verse (P.family.labels.level (grade n)),∃X:Fin 3→Cuts,
        (∀n:Fin 3,Filed (X n) L V B.a i.val s (amp n) δ η
          (WilsonIndependentMatchedFiledIncome.charge e (c n) (α n)) (Shrine (col n) (c n))) ∧
        (∀(S:Finset (Fin 3))(live:S.Nonempty),let g:=seatsFor S live;let slot:=address S live;∀(a B':Fin (g.val+1)→ℝ)(φ:Fin (g.val+1)→Rarity D)
          (y t z:ℝ)(o:CellR),0<t→(∀a b,a≠b→ClearDay (φ a) (φ b) t)→
          (∀s,radiusH (φ s) 1 y  ≤  z)→(∀s,Amplitude (φ s) (B' s))→∀stop  ≤  old V B.a idx,
          let Y:=fun s=>X (slot s)
          let mesh:=fun s=>paceT (Y s).ax.S (Y s).m ((Y s).m+(Y s).i)
          let planted:=fun s=>word (a s • Shrine (col (slot s)) (c (slot s))) (φ s) (mesh s) y o 6
          let fitted:=fun s=>receiving (Y s) (a s/amp (slot s)) (φ s) y o (Y s).i
          let read:=cruises (Y 0).ax (Y 0).tx (Y 0).N ((g.val+1)*k) ((Y 0).m+(Y 0).i) (s+stop)
          response e u (read (MassP G ℝ g.val planted)-read (MassP G ℝ g.val fitted))
            (∑j∈Finset.univ.erase (quiet g.val),toll Y (choose g.val j) b u δ η t z a (fun s=>amp (slot s))
              (fun s=>WilsonIndependentMatchedFiledIncome.charge e (c (slot s)) (α (slot s))) B')) ∧
        (∀(S:Finset (Fin 3))(live:S.Nonempty),let g:=seatsFor S live;let slot:=address S live;∀(flag:Fin (g.val+1)→Bool)
          (a B':Fin (g.val+1)→ℝ)(name:Fin (g.val+1)→Alma (R.F 6))(q:Fin (g.val+1)→ℕ)
          (φ:Fin (g.val+1)→Rarity D)(y t z:ℝ)(o:CellR),(∀s,q s  ≤  e)→0<t→0  ≤  z→(∀s,0  ≤  B' s)→
          (∀v w,v≠w→ClearDay (φ v) (φ w) t)→(∀s,radiusH (φ s) 1 y  ≤  z)→(∀s,Amplitude (φ s) (B' s))→
          let Y:=fun s=>X (slot s)
          let rent:=fun s=>WilsonIndependentMatchedFiledIncome.charge e (c (slot s)) (α (slot s))
          let M:=fun s=>WilsonIndependentMatchedRosterAxes.source (flag s) (a s) (rent s)
          let fields:=fun s=>WilsonIndependentMatchedRosterSlots.entry (flag s) (Y s) (a s/amp (slot s))
            (axis (name s) (q s)) (φ s) y o
          ∀stop  ≤  old V B.a idx,Hearing (Y 0) (ranks flag k 6) u ((Y 0).m+(Y 0).i) (s+stop) (mass fields (Y 0).i)
            (geo g.val e u b (fun s=>degree (flag s) k 6) t z*perSite u b z M B'*
             δ^((counts flag:ℝ)/4-((g.val+3:ℕ):ℝ)*η))):=by
  have wide:1 ≤ (b:ℝ)-((3*6:ℕ):ℝ)-(3:ℝ)/4:=by norm_num at *;exact gap
  obtain ⟨α,apos,course⟩:=WilsonIndependentMatchedRosterBundle.original R chart kernel V B premium phase
    P W kind grade limit p (fun i=>(limit i).trans v.hk) v covered dim input test 3 u b room join output wide η positive
  refine ⟨α,apos,?_⟩
  filter_upwards [course] with idx program i same δ amp cir N
  obtain ⟨A,s,ker,patch,L,draw,rat,anchor,ages,fees,files⟩:=program i same
  refine ⟨A,s,ker,patch,L,draw,rat,anchor,ages,fees,?_⟩
  intro c
  obtain ⟨X,filed,raw,basis⟩:=files c
  exact ⟨X,filed,fun S live=>raw (seatsFor S live) (address S live),fun S live=>basis (seatsFor S live) (address S live)⟩

end YM.Integration.WilsonIndependentMatchedRosterRose
