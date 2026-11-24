import YM.Integration.WilsonIndependentMatchedReportedContrast
import YM.Integration.WilsonOriginalPublicPlantedOlderContrast

/-! The complete raw and fitted pair use one real normalized Wilson cover
from the elected fine top, through their appointed report and all the way
to each eligible older stop. The deposited scalar is heard there. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedStoppedContrast
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedSeatedIncome WilsonIndependentMatchedCoveredSeats
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}

open WilsonIndependentMatchedCutBudget WilsonIndependentMatchedFittedSeat

open WilsonIndependentMatchedMixBudget WilsonIndependentMatchedCoverReception

open WilsonIndependentMatchedReportedContrast
open WilsonIndependentEvenPassport (old count)

def value (X:CutsP H T p v E W K U)(b:ℕ)(A B:Era G ℝ):Era G ℝ:=
  cruises X.ax X.tx X.N (k+k) X.N b (agateV A B)

theorem original (u b base:ℕ)(w s:Credit)(run:XSpace.Run)(B₀ η:ℝ)(nonneg:0 ≤ B₀)(small:0<η)
    (room:u+b ≤ u₀)(gap:1 ≤ (b:ℝ)-((h+h:ℕ):ℝ)-(2:ℝ)/4):
    ∀ᶠ idx:ℕ in atTop,∀(X Y:CutsP H T p v E W K U)(a c:ℝ)(φ ψ:Rarity D)
    (y t z B D₀:ℝ)(o:CellR),let δ:=(run.step idx).spacing
    Y.L=X.L → Y.m=X.m → Y.N=X.N → Y.i=X.i →
    ∀f:ℕ,X.vesselsC.anchor=f → X.m=f+old run base idx → X.N=f+count run base idx → X.m+X.i=X.N →
    (∀t ≤ old run base idx,X.vesselsC.y (f+t) ≤ B₀) →
    WilsonOriginalPublicPlantedStableCredit.span X X.i=-Real.log δ →
    SpringD X.vesselsC (k+k) u b w → Dormitory X.vesselsC (k+k) u s → Dormitory X.vesselsC (k+h) u s →
    0<t → ClearDay φ ψ t → radiusH φ 1 y ≤ z → radiusH ψ 1 y ≤ z →
    0 ≤ B → 0 ≤ D₀ → Amplitude φ B → Amplitude ψ D₀ →
    let raw₁:=raw X a φ y o;let raw₂:=raw Y c ψ y o
    let fit₁:=receiving X a φ y o X.i;let fit₂:=receiving Y c ψ y o Y.i
    let wage:=δ^(-η)*expense X Y a c φ ψ u b y t z δ η B D₀
    ∀stop ≤ old run base idx,
      let R:=value X (f+stop) raw₁ raw₂;let F:=value X (f+stop) fit₁ fit₂
      Flush e u 1 (R-F) wage ∧ ∀j ≤ e,∀z₀:Fin 0 → YForest G,‖R.2 j 0 z₀-F.2 j 0 z₀‖ ≤ wage:=by
  filter_upwards [WilsonIndependentMatchedReportedContrast.original (H:=H) (T:=T) (p:=p) (v:=v)
      (E:=E) (W:=W) (K:=K) (U:=U) u b w s run B₀ η small room gap,
    WilsonOriginalPublicPlantedOlderContrast.original G (k+k) e u E s run base B₀ η nonneg small] with idx fieldPay later
  intro X Y a c φ ψ y t z B D₀ o δ school home ceiling steps f source report top enters
    house clock sale store both ht sep pcap qcap hB hD φpaid ψpaid raw₁ raw₂ fit₁ fit₂ wage stop early R₀ F₀
  have land:X.vesselsC.y X.m ≤ B₀:=report ▸ house _ le_rfl
  obtain ⟨rp,fp,heard⟩:=fieldPay X Y a c φ ψ y t z B D₀ o school home ceiling steps land clock
    sale store both ht sep pcap qcap hB hD φpaid ψpaid
  let P:=agateV raw₁ raw₂;let Q:=agateV fit₁ fit₂
  have real:old run base idx ≤ count run base idx:=Nat.le_add_right _ _
  have paid:Flush e u 1 (cruises X.ax X.tx (f+count run base idx) (k+k) (f+count run base idx)
    (f+old run base idx) P-cruises X.ax X.tx (f+count run base idx) (k+k) (f+count run base idx)
    (f+old run base idx) Q) (expense X Y a c φ ψ u b y t z δ η B D₀):=by
    have eigen:Flush e u 1 (cruises X.ax X.tx X.N (k+k) (X.m+X.i) X.m P-
      cruises X.ax X.tx X.N (k+k) (X.m+X.i) X.m Q) _:=heard
    rw [enters] at eigen
    simpa only [←top,←report] using eigen
  have result:=later X.vesselsC store f source house stop (old run base idx) (count run base idx) early
    le_rfl real le_rfl P Q rp fp _ paid
  dsimp only at result
  dsimp only [R₀,F₀,wage,value,δ,P,Q] at result ⊢
  rw [←top] at result
  exact result

end YM.Integration.WilsonIndependentMatchedStoppedContrast
