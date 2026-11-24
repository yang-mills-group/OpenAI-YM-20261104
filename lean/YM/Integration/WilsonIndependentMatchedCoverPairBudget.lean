import YM.Integration.WilsonIndependentMatchedCoverReception
import YM.Integration.WilsonIndependentMatchedCoverDouble

/-! The complete pair of compensated, located shots on a single matched
cut reaches its true reporter with a gain from each designated slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverPairBudget
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedSeatedIncome WilsonIndependentMatchedCoveredSeats
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}

def Bought (X:CutsP H T p v E W K U)(a δ A:ℝ):Prop:=
  ∀i ≤ X.i,∀j ≤ e,∀r:ℕ,∀u ≤ u₀,Fruit 0 1 u ((a • X.springP i).2 j r)
    (A*(δ/paceT X.ax.S X.m (X.m+i))^(1/4:ℝ))

theorem original (u b:ℕ)(w s:Credit)(run:XSpace.Run)(B₀ η:ℝ)(small:0<η)
    (room:u+b ≤ u₀)(gap:1 ≤ (b:ℝ)-((h+h:ℕ):ℝ)-(2:ℝ)/4):
    ∀ᶠ idx:ℕ in atTop,∀(X Y:CutsP H T p v E W K U)(a c:ℝ)(φ ψ:Rarity D)
    (y t z A B C D₀:ℝ)(o:CellR),let δ:=(run.step idx).spacing
    Y.L=X.L → Y.m=X.m → Y.N=X.N → Y.i=X.i →
    X.vesselsC.y X.m ≤ B₀ → WilsonOriginalPublicPlantedStableCredit.span X X.i=-Real.log δ →
    SpringD X.vesselsC (k+k) u b w → Dormitory X.vesselsC (k+k) u s →
    0<t → ClearDay φ ψ t → radiusH φ 1 y ≤ z → radiusH ψ 1 y ≤ z →
    0 ≤ A → 0 ≤ B → 0 ≤ C → 0 ≤ D₀ → Amplitude φ B → Amplitude ψ D₀ →
    Bought X a δ A → Bought Y c δ C →
    let whole:=cruises X.ax X.tx X.N (k+k) (X.m+X.i) X.m
      (agateV (seat X a φ y o X.i) (seat Y c ψ y o X.i))
    Auth (k+k) whole ∧ Flush e u 1 whole
      (WilsonIndependentMatchedCoverReception.rate k k e u b h h φ ψ y t z δ η A B C D₀*δ^((2:ℝ)/4)):=by
  have clearance:1 ≤ (b:ℝ)-((h+h:ℕ):ℝ)-((1+1:ℕ):ℝ)/4:=by norm_num at gap ⊢;exact gap
  filter_upwards [WilsonIndependentMatchedCoverReception.original (H:=H) (T:=T) (p:=p) (v:=v)
    (E:=E) (W:=W) (K:=K) (U:=U) (D₁:=D) (D₂:=D) k k (k+k) u b h h 1 1 w s
    run B₀ η small le_rfl (by decide) clearance] with idx price
  intro X Y a c φ ψ y t z A B C D₀ o δ school home ceiling steps land clock sale store
    ht sep pcap qcap hA hB hC hD φpaid ψpaid xpath ypath whole
  have realm:Y.vesselsC=X.vesselsC:=congrArg (fun z=>z.L.V) school
  have paidX:=WilsonIndependentMatchedSeatedIncome.stable X a φ y o δ A B φpaid u b room xpath
  have paidY:=WilsonIndependentMatchedSeatedIncome.stable Y c ψ y o δ C D₀ ψpaid u b room ypath
  rw [realm,home,steps] at paidY
  have read:=price X φ ψ y t z A B C D₀ o (seat X a φ y o) (seat Y c ψ y o) land clock sale store
    ht sep pcap qcap hA hB hC hD (joined X Y school home ceiling steps a c φ ψ y o)
    (by simpa only [Nat.cast_one] using paidX) (by simpa only [Nat.cast_one] using paidY)
  simpa only [show ((1+1:ℕ):ℝ)=(2:ℝ) by norm_num] using read

end YM.Integration.WilsonIndependentMatchedCoverPairBudget
