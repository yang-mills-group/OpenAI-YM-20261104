import YM.Integration.WilsonIndependentMatchedTotalTop

/-! The complete two-input raw-minus-fitted contrast on the genuine common
Wilson cover, including the occupied scalar at the report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedReportedContrast
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

def raw (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR):Era G ℝ:=
  word (a • X.pt) φ (paceT X.ax.S X.m (X.m+X.i)) y o h

def expense (X Y:CutsP H T p v E W K U)(a c:ℝ)(φ ψ:Rarity D)(u b:ℕ)
    (y t z δ η B D₀:ℝ):ℝ:=
  let ax:=restored X a δ η;let ay:=restored Y c δ η
  let px:=fee X a u b;let py:=fee Y c u b
  rate k k e u b h h φ ψ y t z δ η ax B ay D₀*δ^((2:ℝ)/4)+
  rate k h e u b h h φ ψ y t z δ η ax B py D₀*δ^(1/4:ℝ)+
  rate h k e u b h h φ ψ y t z δ η px B ay D₀*δ^(1/4:ℝ)

private lemma plus {A B:ℝ}{Z V:Era G ℝ}{u:ℕ}(p:Flush e u 1 Z A)(q:Flush e u 1 V B):
    Flush e u 1 (Z+V) (A+B):=⟨add_nonneg p.1 q.1,fun i hi j hj=>(p.2 i hi j hj).plus (q.2 i hi j hj) zero_le_one⟩

theorem original (u b:ℕ)(w s:Credit)(run:XSpace.Run)(B₀ η:ℝ)(small:0<η)
    (room:u+b ≤ u₀)(gap:1 ≤ (b:ℝ)-((h+h:ℕ):ℝ)-(2:ℝ)/4):
    ∀ᶠ idx:ℕ in atTop,∀(X Y:CutsP H T p v E W K U)(a c:ℝ)(φ ψ:Rarity D)
    (y t z B D₀:ℝ)(o:CellR),let δ:=(run.step idx).spacing
    Y.L=X.L → Y.m=X.m → Y.N=X.N → Y.i=X.i →
    X.vesselsC.y X.m ≤ B₀ → WilsonOriginalPublicPlantedStableCredit.span X X.i=-Real.log δ →
    SpringD X.vesselsC (k+k) u b w → Dormitory X.vesselsC (k+k) u s → Dormitory X.vesselsC (k+h) u s →
    0<t → ClearDay φ ψ t → radiusH φ 1 y ≤ z → radiusH ψ 1 y ≤ z →
    0 ≤ B → 0 ≤ D₀ → Amplitude φ B → Amplitude ψ D₀ →
    let raw₁:=raw X a φ y o;let raw₂:=raw Y c ψ y o
    let fit₁:=receiving X a φ y o X.i;let fit₂:=receiving Y c ψ y o Y.i
    Auth (k+k) (agateV raw₁ raw₂) ∧ Auth (k+k) (agateV fit₁ fit₂) ∧
      Flush e u 1 (field X raw₁ raw₂-field X fit₁ fit₂) (expense X Y a c φ ψ u b y t z δ η B D₀):=by
  have easy:1 ≤ (b:ℝ)-((h+h:ℕ):ℝ)-(1:ℝ)/4:=by linarith only [gap]
  filter_upwards [WilsonIndependentMatchedCutBudget.original (H:=H) (T:=T) (p:=p) (v:=v)
      (E:=E) (W:=W) (K:=K) (U:=U) run B₀ η small,
    WilsonIndependentMatchedMixBudget.original (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W) (K:=K) (U:=U)
      u b w s run B₀ η small room easy,
    WilsonIndependentMatchedCoverPairBudget.original (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W)
      (K:=K) (U:=U) u b w s run B₀ η small room gap] with idx unary mixedPair twice
  intro X Y a c φ ψ y t z B D₀ o δ school home ceiling steps land clock sale store bothStore
    ht sep pcap qcap hB hD φpaid ψpaid raw₁ raw₂ fit₁ fit₂
  let sx:=seat X a φ y o X.i;let sy:=seat Y c ψ y o Y.i
  let A:=restored X a δ η;let C:=restored Y c δ η
  have realm:Y.vesselsC=X.vesselsC:=congrArg (fun z=>z.L.V) school
  have landY:Y.vesselsC.y Y.m ≤ B₀:=by rw [realm,home];exact land
  have clockY:WilsonOriginalPublicPlantedStableCredit.span Y Y.i=-Real.log δ:=by
    unfold WilsonOriginalPublicPlantedStableCredit.span
    rw [realm,steps,home];exact clock
  have hs:SpringD Y.vesselsC (k+k) u b w:=realm.symm ▸ sale
  have hb:Dormitory Y.vesselsC (k+h) u s:=realm.symm ▸ bothStore
  have reverse:ClearDay ψ φ t:=fun a ha b hb=>dist_comm a b ▸ sep b hb a ha
  have hA:0 ≤ A:=mul_nonneg (abs_nonneg _) (mul_nonneg (Real.rpow_nonneg (run.step idx).positive.le _) X.hf)
  have hC:0 ≤ C:=mul_nonneg (abs_nonneg _) (mul_nonneg (Real.rpow_nonneg (run.step idx).positive.le _) Y.hf)
  have D₁:=(twice X Y a c φ ψ y t z A B C D₀ o school home ceiling steps land clock sale store ht sep
    pcap qcap hA hB hC hD φpaid ψpaid (unary X a land clock) (unary Y c landY clockY)).2
  have D₂:=(mixedPair X Y a c φ ψ y t z B D₀ o school home ceiling steps land clock sale bothStore
    ht sep pcap qcap hB hD φpaid ψpaid).1.2
  have D₃:=(mixedPair Y X c a ψ φ y t z D₀ B o school.symm home.symm ceiling.symm steps.symm
    landY clockY hs hb ht reverse qcap pcap hD hB ψpaid φpaid).2.2
  have same (P Q:Era G ℝ):field Y P Q=field X P Q:=by
    change cruises Y.vesselsC.draws Y.vesselsC.paid Y.N (k+k) (Y.m+Y.i) Y.m (agateV P Q)=_
    rw [realm,ceiling,home,steps];rfl
  rw [same] at D₃
  have first:raw₁=sx+fit₁:=WilsonIndependentMatchedTotalTop.placed X a φ y o
  have second:raw₂=sy+fit₂:=WilsonIndependentMatchedTotalTop.placed Y c ψ y o
  have hx:=((traced X a φ y o).1 X.i le_rfl)
  have hy:=((traced Y c ψ y o).1 Y.i le_rfl)
  have p1:=((funds X a φ y o δ B φpaid u b).head X.i le_rfl).tall v.hk
  have p2:=((funds Y c ψ y o δ D₀ ψpaid u b).head Y.i le_rfl).tall v.hk
  rw [first,second]
  refine ⟨(hx.add p1).manor (hy.add p2),p1.manor p2,?_⟩
  rw [show field X (sx+fit₁) (sy+fit₂)-field X fit₁ fit₂=
    field X sx sy+field X sx fit₂+field X fit₁ sy from
    WilsonIndependentMatchedTotalTop.transferred X.vesselsC (Nat.le_add_right X.m X.i)
      (X.hc.trans X.hn) sx sy fit₁ fit₂ hx hy p1 p2]
  dsimp only [sx,sy,fit₁,fit₂,field,expense]
  simpa only [steps,field,A,C] using plus (plus D₁ D₂) D₃

end YM.Integration.WilsonIndependentMatchedReportedContrast
