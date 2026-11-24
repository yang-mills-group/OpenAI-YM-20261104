import YM.Integration.WilsonIndependentMovingRosterNormalizedEscrow
import YM.Integration.WilsonIndependentMovingRosterAllFineFunded

/-! Read the fully compensated n-child source through every scalar grade and retain the true higher Taylor orders. -/
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedRead

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterTariff (factor)
open WilsonIndependentMovingRosterStableSale (homes centers)
open WilsonIndependentMovingRosterLaneFilm (Licensed)
open WilsonIndependentMatchedRosterPowers (profiles)
open WilsonIndependentMatchedRosterSlots (degree count entry wallet)
open WilsonIndependentMatchedRosterMasks (Bits choose placed)
open WilsonIndependentMatchedRosterCuts (counts ranks)
open WilsonIndependentMovingRosterTopFields (stable fitted)
open WilsonIndependentMatchedFittedSeat (dose)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedRosterMasks (quiet present)
open WilsonIndependentMatchedCoverDate (age)
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Elected Named needed)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonIndependentMovingRosterBirthCalendar (room)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonIndependentMatchedReportedProxy (sectionSeal)

theorem graded {e:ℕ}{f:ℕ→ℝ}{B:ℝ}(salary:∀q≤e,‖f q‖≤B):Heard e 0 1 B f:=by
  have money:0≤B:=(norm_nonneg (f 0)).trans (salary 0 (Nat.zero_le _))
  simp only [Heard,pow_zero,inv_one,one_mul]
  refine ⟨salary,fun g g0 g1=>⟨?_,fun J=>?_⟩⟩
  · apply (norm_sum_le ..).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro q hq
    rw [norm_mul,Real.norm_of_nonneg (pow_nonneg g0 _)]
    exact mul_le_mul_of_nonneg_left (salary q (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))) (pow_nonneg g0 _)
  · simpa only [pow_zero,inv_one,one_mul] using
      WilsonSeparatedPrefixMovingHighGrades.original J e 0 g 1 B f g0 g1 zero_lt_one money
        (fun q _ hq=>by simpa only [pow_zero,inv_one,one_mul] using salary q hq)

variable {G:Gauge}{H:Hol G}{n e h D k u₀:ℕ}{F:Labels.Frame G h}{T:SectionData F}
    {p:h<D}{v:Rails h k u₀ e}{W K U:Credit}
local notation "L₀" => Credit.leanC
local notation "Qₙ" => (fun _:Fin (n+1)=>sectionSeal T p)
local notation "Qₐ" => sectionSeal T p

def nominalFee (R:Realm G (e+1) L₀)(col:Fin ((n+1)+1)→Verse F)(B:Fin ((n+1)+1)→ℝ)
    (first shape chron:Credit)(u target older m:ℕ)(gap z y outer:ℝ):ℝ:=
  let l:=h+capP Qₙ
  let τ:=target+l
  let a:=h+(u+τ)
  let b:=capP Qₙ+h+(u+τ+2)
  let Z:=epoch R older m
  let fresh:=WilsonSeparatedPrefixMovingUnformedSector.invoice Qₙ Qₐ (Fin.tail col) (col 0) e l u b z outer (B 0) (Fin.tail B)
  let formed:=shape.buy (room z gap y)*WilsonIndependentMovingRosterInvoice.charge Qₙ Qₐ (Fin.tail col) (col 0)
    e u a z outer (B 0) (Fin.tail B)
  2*fresh*first.buy Z+4*formed*chron.buy Z

theorem original {height seats:ℕ}(M:Master H)(named:Named M height seats Qₐ)(u target:ℕ)(positive:0<target)
    (finance:needed (h+capP Qₙ) u target ≤ seats):
    ∃first shape chron:Credit,∀(R:Realm G (e+1) L₀)(_resident:Elected M R height seats)
      (X:Fin ((n+1)+1)→CutsP H T p v L₀ W K U)(older t m N:ℕ)(_live:R.anchor ≤ older)
      (_ear:older ≤ t)(_away:t ≤ m)(_upper:m ≤ N)(a:Fin ((n+1)+1)→ℝ)(col:Fin ((n+1)+1)→Verse F)
      (φ:Fin ((n+1)+1)→Rarity D)(B:Fin ((n+1)+1)→ℝ)(o:CellR)(y z gap outer correction:ℝ),
      let zoom:=paceT R.draws.S m t
      let c:Fin ((n+1)+1)→ℝ:=centers y zoom
      (∀s,Amplitude (φ s) (B s)) → (∀s,radiusH (φ s) 1 (c s)≤z) →
      (∀i j:Fin (n+1),i≠j→ClearDay (φ i.succ) (φ j.succ) gap) →
      (∀i:Fin (n+1),∀p∈tsupport (φ i.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,zoom*outer≤dist p (zoom • q)) →
      (∀q∈tsupport (φ 0).ψ.val,zoom*outer+1+|y|≤‖zoom • q‖) →
      0<gap → 0<outer → 2+2*|y|≤z →
      (∀q≤e,∀ω:Fin 0→YForest G,
        ‖(WilsonIndependentMovingRosterNormalizedBook.raw R X a col φ y o t m older N).2 q 0 ω-
          (WilsonIndependentMovingRosterNormalizedBook.prescribed R X col φ y o t m older N).2 q 0 ω‖≤correction) →
      ∀ω:Fin 0→YForest G,
        Heard e 0 1 ((zoom^target)⁻¹*(nominalFee (n:=n) (T:=T) (p:=p) R col B first shape chron
          u target older m gap z y outer)+correction)
          (fun q=>(WilsonIndependentMovingRosterNormalizedBook.raw R X a col φ y o t m older N).2 q 0 ω):=by
  obtain ⟨first,shape,chron,nominal⟩:=WilsonIndependentMovingRosterAllFineFunded.original M Qₙ Qₐ
    e u target positive (fun _=>named) named finance
  refine ⟨first,shape,chron,?_⟩
  intro R resident X older t m N live ear away upper a col φ B o y z gap outer correction zoom c amp rad near far cover gap0 outer0 centered earn ω
  have inside (i:Fin (n+1)):(φ i.succ).radius+|y|+1≤z:=by
    simpa only [radiusH,c,WilsonIndependentMovingRosterStableSale.centers,Fin.cons_succ,abs_one] using rad i.succ
  have outside:(φ 0).radius+|y/zoom|+1≤z:=by
    simpa only [radiusH,c,WilsonIndependentMovingRosterStableSale.centers,Fin.cons_zero,abs_one] using rad 0
  have source:=nominal R resident older t m N live ear away upper (Fin.tail φ) (φ 0) (Fin.tail col) (col 0) o y z gap
    outer (B 0) (Fin.tail B) gap0 outer0 (fun s=>amp s.succ) (amp 0) near far cover inside outside centered ω
  apply graded
  intro q hq
  let raw:=(WilsonIndependentMovingRosterNormalizedBook.raw R X a col φ y o t m older N).2 q 0 ω
  let scalar:=(WilsonIndependentMovingRosterNormalizedBook.prescribed R X col φ y o t m older N).2 q 0 ω
  let fare:=nominalFee (n:=n) (T:=T) (p:=p) R col B first shape chron u target older m gap z y outer
  have issued:‖scalar‖≤(zoom^target)⁻¹*fare:=source.1 q hq
  have all:‖raw-scalar‖≤correction:=earn q hq ω
  calc ‖raw‖=‖(raw-scalar)+scalar‖:=by rw [sub_add_cancel]
       _ ≤ ‖raw-scalar‖+‖scalar‖:=norm_add_le _ _
       _ ≤ _:=by linarith only [all,issued]

end YM.Integration.WilsonIndependentMovingRosterNormalizedRead
