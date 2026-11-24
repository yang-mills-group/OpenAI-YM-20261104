import YM.Integration.WilsonIndependentMatchedFittedSeat
import YM.Integration.WilsonIndependentMatchedCutBudget
import YM.Integration.WilsonIndependentMatchedCoverGrade

/-! Both orders of the actual fitted and compensated products on the common
cover. Their physical engineering degree is the common enrolled horizon.
Their upper angular truncation may be raised to the common pair degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedMixBudget
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

def field (X:CutsP H T p v E W K U)(P Q:Era G ℝ):Era G ℝ:=
  cruises X.ax X.tx X.N (k+k) (X.m+X.i) X.m (agateV P Q)

def Priced (u:ℕ)(P:Era G ℝ)(k e:ℕ)(A:ℝ):Prop:=Auth k P ∧ Flush e u 1 P A

private lemma promote (X:CutsP H T p v E W K U)(P Q:Era G ℝ)(l r u:ℕ)(A:ℝ)
    (less:l+r ≤ k+k)(auth:Auth (l+r) (agateV P Q))
    (price:Priced u (cruises X.ax X.tx X.N (l+r) (X.m+X.i) X.m (agateV P Q)) (l+r) e A):
    Priced u (field X P Q) (k+k) e A:=by
  have eqn:=WilsonIndependentMatchedCoverGrade.carried X.ax X.tx X.vesselsC.hG X.vesselsC.green
    (Nat.le_add_right X.m X.i) (X.hc.trans X.hn) (agateV P Q) auth less
  unfold Priced field
  rw [←eqn]
  exact ⟨price.1.tall less,price.2⟩

theorem original (u b:ℕ)(w s:Credit)(run:XSpace.Run)(B₀ η:ℝ)(small:0<η)
    (room:u+b ≤ u₀)(gap:1 ≤ (b:ℝ)-((h+h:ℕ):ℝ)-(1:ℝ)/4):
    ∀ᶠ idx:ℕ in atTop,∀(X Y:CutsP H T p v E W K U)(a c:ℝ)(φ ψ:Rarity D)
    (y t z B D₀:ℝ)(o:CellR),let δ:=(run.step idx).spacing
    Y.L=X.L → Y.m=X.m → Y.N=X.N → Y.i=X.i →
    X.vesselsC.y X.m ≤ B₀ → WilsonOriginalPublicPlantedStableCredit.span X X.i=-Real.log δ →
    SpringD X.vesselsC (k+k) u b w → Dormitory X.vesselsC (k+h) u s →
    0<t → ClearDay φ ψ t → radiusH φ 1 y ≤ z → radiusH ψ 1 y ≤ z →
    0 ≤ B → 0 ≤ D₀ → Amplitude φ B → Amplitude ψ D₀ →
    let A:=restored X a δ η;let C:=fee Y c u b;let P:=seat X a φ y o X.i;let F:=receiving Y c ψ y o X.i
    Priced u (field X P F) (k+k) e (WilsonIndependentMatchedCoverReception.rate k h e u b h h φ ψ
      y t z δ η A B C D₀*δ^(1/4:ℝ)) ∧
    Priced u (field X F P) (k+k) e (WilsonIndependentMatchedCoverReception.rate h k e u b h h ψ φ
      y t z δ η C D₀ A B*δ^(1/4:ℝ)):=by
  have gh:1 ≤ (b:ℝ)-((h+h:ℕ):ℝ)-((1+0:ℕ):ℝ)/4:=by simpa only [Nat.add_zero,Nat.cast_one] using gap
  have hg:1 ≤ (b:ℝ)-((h+h:ℕ):ℝ)-((0+1:ℕ):ℝ)/4:=by simpa only [Nat.zero_add,Nat.cast_one] using gap
  have kroom:k+h ≤ k+k:=Nat.add_le_add_left v.hk k
  have hroom:h+k ≤ k+k:=Nat.add_le_add_right v.hk k
  filter_upwards [WilsonIndependentMatchedCutBudget.original (H:=H) (T:=T) (p:=p) (v:=v)
    (E:=E) (W:=W) (K:=K) (U:=U) run B₀ η small,
    WilsonIndependentMatchedCoverReception.original (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W)
      (K:=K) (U:=U) (D₁:=D) (D₂:=D) k h (k+k) u b h h 1 0 w s run B₀ η small kroom (by decide) gh,
    WilsonIndependentMatchedCoverReception.original (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W)
      (K:=K) (U:=U) (D₁:=D) (D₂:=D) h k (k+k) u b h h 0 1 w s run B₀ η small hroom (by decide) hg]
    with idx bought left right
  intro X Y a c φ ψ y t z B D₀ o δ school home ceiling steps land clock sale store
    ht sep pcap qcap hB hD φpaid ψpaid A C P F₀
  have realm:Y.vesselsC=X.vesselsC:=congrArg (fun z=>z.L.V) school
  have hA:0 ≤ A:=mul_nonneg (abs_nonneg _) (mul_nonneg (Real.rpow_nonneg (run.step idx).positive.le _) X.hf)
  have hC:0 ≤ C:=WilsonIndependentMatchedFittedSeat.nn Y c u b
  have cashX:=WilsonIndependentMatchedSeatedIncome.stable X a φ y o δ A B φpaid u b room (bought X a land clock)
  have cashY:=funds Y c ψ y o δ D₀ ψpaid u b
  rw [realm,home,steps] at cashY
  have trace:=along X Y school home ceiling a c φ ψ y o
  have reverse:ClearDay ψ φ t:=fun a ha b hb=>dist_comm a b ▸ sep b hb a ha
  have hs:Dormitory X.vesselsC (h+k) u s:=by rw [Nat.add_comm h k];exact store
  have fwd:=left X φ ψ y t z A B C D₀ o (seat X a φ y o) (receiving Y c ψ y o)
    land clock sale store ht sep pcap qcap hA hB hC hD trace.1
    (by simpa only [Nat.cast_one] using cashX) (by simpa only [Nat.cast_zero,zero_div] using cashY)
  have rev:=right X ψ φ y t z C D₀ A B o (receiving Y c ψ y o) (seat X a φ y o)
    land clock sale hs ht reverse qcap pcap hC hD hA hB trace.2
    (by simpa only [Nat.cast_zero,zero_div] using cashY) (by simpa only [Nat.cast_one] using cashX)
  have authP:=cashX.head X.i le_rfl
  have authF:=cashY.head X.i le_rfl
  constructor
  · apply promote X P F₀ k h _ _ kroom (authP.manor authF)
    simpa only [Priced,Nat.add_zero,Nat.cast_one] using fwd
  · apply promote X F₀ P h k _ _ hroom (authF.manor authP)
    simpa only [Priced,Nat.zero_add,Nat.cast_one] using rev

end YM.Integration.WilsonIndependentMatchedMixBudget
