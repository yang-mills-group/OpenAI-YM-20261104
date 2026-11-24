import YM.Integration.WilsonIndependentMatchedCoverFlush
import YM.Integration.WilsonIndependentMatchedCoverSalary
import YM.Integration.WilsonIndependentMatchedSeatedIncome

/-! The complete native two-source field at its true reporting scale, bounded
before the later normalized integration and with one input fee per seat. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverReception
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedSeatedIncome WilsonIndependentMatchedCoveredSeats
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}

def rate {D₁ D₂:ℕ}(l r e u b d₁ d₂:ℕ)(φ:Rarity D₁)(ψ:Rarity D₂)
    (y t z δ η A B C D₀:ℝ):ℝ:=
  coinMat (l+r) e*WilsonIndependentMatchedCoverHome.bill φ u d₁ y A B*
    WilsonIndependentMatchedCoverHome.bill ψ u d₂ y C D₀+
    2*(δ^(-η)*WilsonIndependentMatchedCoverSalary.profile u b t z z z A B C D₀)

private lemma add {P Q:Era G ℝ}{u e:ℕ}{A B:ℝ}(f:Flush e u 1 P A)(g:Flush e u 1 Q B):
    Flush e u 1 (P+Q) (A+B):=
  ⟨add_nonneg f.1 g.1,fun i hi j hj=>(f.2 i hi j hj).plus (g.2 i hi j hj) zero_le_one⟩

/-- This receives two actual independently submitted rooted seats on the same
realm. An empty seat contributes zero. The joined and still-unjoined incomes
have the same designated power, including on the genuine unit. -/
theorem original {D₁ D₂:ℕ}(l r bound u b d₁ d₂ n₁ n₂:ℕ)(w s:Credit)
    (run:XSpace.Run)(B₀ η:ℝ)(ηpos:0<η)(room:l+r ≤ bound)(steps:n₁+n₂ ≤ 4)
    (clear:1 ≤ (b:ℝ)-((d₁+d₂:ℕ):ℝ)-((n₁+n₂:ℕ):ℝ)/4):
    ∀ᶠ idx:ℕ in atTop,∀(X:CutsP H T p v E W K U)(φ:Rarity D₁)(ψ:Rarity D₂)
    (y t z A B C D₀:ℝ)(o:CellR)(P Q:ℕ → Era G ℝ),
    let δ:=(run.step idx).spacing
    X.vesselsC.y X.m ≤ B₀ → WilsonOriginalPublicPlantedStableCredit.span X X.i=(-Real.log δ) →
    SpringD X.vesselsC bound u b w → Dormitory X.vesselsC (l+r) u s →
    0<t → ClearDay φ ψ t → radiusH φ 1 y ≤ z → radiusH ψ 1 y ≤ z →
    0 ≤ A → 0 ≤ B → 0 ≤ C → 0 ≤ D₀ →
    Posted X.vesselsC l r X.m X.N X.i P Q →
    Funds X.vesselsC l d₁ X.m X.i u b φ y o δ ((n₁:ℝ)/4) A B P →
    Funds X.vesselsC r d₂ X.m X.i u b ψ y o δ ((n₂:ℝ)/4) C D₀ Q →
    let whole:=cruises X.ax X.tx X.N (l+r) (X.m+X.i) X.m (agateV (P X.i) (Q X.i))
    Auth (l+r) whole ∧ Flush e u 1 whole
      (rate l r e u b d₁ d₂ φ ψ y t z δ η A B C D₀*δ^(((n₁+n₂:ℕ):ℝ)/4)):=by
  obtain ⟨credit,date⟩:=WilsonIndependentMatchedCoverDate.original (D:=D₁) (D':=D₂) G
    l r bound e u b d₁ d₂ E w s
  filter_upwards [WilsonIndependentMatchedCoverCap.earned (H:=H) (T:=T) (p:=p) (v:=v)
    (E:=E) (W:=W) (K:=K) (U:=U) run credit (priceWG G e bound u b E w) (d₁+d₂) B₀ η ηpos] with idx money
  intro X φ ψ y t z A B C D₀ o P Q δ land clock sale older ht sep pcap qcap hA hB hC hD book ca cb
  let α:ℝ:=(n₁:ℝ)/4
  let β:ℝ:=(n₂:ℝ)/4
  let M:=δ^(-η)*WilsonIndependentMatchedCoverSalary.profile u b t z z z A B C D₀
  have expn:α+β=((n₁+n₂:ℕ):ℝ)/4:=by dsimp only [α,β];push_cast;ring
  have ok:α+β ≤ 1:=by
    rw [expn]
    have sn:((n₁+n₂:ℕ):ℝ) ≤ 4:=by exact_mod_cast steps
    linarith
  have top:0<δ:=(run.step idx).positive
  have Mpos:0 ≤ M:=mul_nonneg (Real.rpow_nonneg top.le _)
    (WilsonIndependentMatchedCoverSalary.nonneg u b ht.le (zero_le_one.trans ((fieldCap φ 1 y).trans pcap)) hA hB hC hD)
  have endDate:X.m+X.i ≤ X.N:=X.hc.trans X.hn
  have each (i:ℕ)(hi:i<X.i):
      let v:=paceT X.ax.S X.m (X.m+i)
      Flush e u 1 (cruises X.ax X.tx X.N (l+r) (X.m+i) X.m
        (JoinGap X.ax X.tx (X.m+i) X.N l r (P (i+1)) (Q (i+1))))
        (M*v^((b:ℝ)-((d₁+d₂:ℕ):ℝ))*(δ/v)^(((n₁+n₂:ℕ):ℝ)/4)):=by
    let z₀:=paceT X.ax.S X.m (X.m+i)
    let x:=paceT X.ax.S X.m (X.m+(i+1))
    have hni:X.m+i<X.N:=(Nat.add_lt_add_left hi X.m).trans_le endDate
    have hx:0<x:=pace_pos ..
    have hz:0<z₀:=pace_pos ..
    have hsmall:x ≤ 1:=pace_le _ (Nat.le_add_right ..)
    have hv:z₀ ≤ 1:=pace_le _ (Nat.le_add_right ..)
    have fit {d:ℕ}(f:Rarity d):radiusH f z₀ y ≤ radiusH f 1 y:=by
      unfold radiusH;rw [abs_of_pos hz,abs_one];linarith
    by_cases fresh:(VisitsT φ x y o).Nonempty ∧ (VisitsT ψ x y o).Nonempty
    · have paid:=(date X.vesselsC sale older X.m (X.m+i) X.N X.ha (Nat.le_add_right ..) hni room φ ψ
          (P (i+1)) (Q (i+1)) δ y t z α β A B C D₀ o top sep ht ((fit φ).trans pcap)
          ((fit ψ).trans qcap) fresh.1 fresh.2 (ca.cash i hi) (cb.cash i hi)).1
      have charges:=WilsonIndependentMatchedCoverSalary.original credit w X.vesselsC d₁ d₂ bound u b
        X.m (X.m+i) φ ψ y t z α β A B C D₀ (δ^(-η)) x rfl hx hsmall ht.le (Real.rpow_nonneg top.le _)
        hA hB hC hD pcap qcap (money X land clock i hi.le α β ok)
      have inc:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right charges
        (Real.rpow_nonneg hz.le ((b:ℝ)-((d₁+d₂:ℕ):ℝ)))) (Real.rpow_nonneg (div_nonneg top.le hz.le) (α+β))
      rw [←expn]
      exact ⟨paid.1.trans inc,fun j hj r hr=>(paid.2 j hj r hr).more inc⟩
    · have gone:P (i+1)=0 ∨ Q (i+1)=0:=by
        by_cases a:(VisitsT φ x y o).Nonempty
        · exact Or.inr (cb.empty i hi fun b=>fresh ⟨a,b⟩)
        · exact Or.inl (ca.empty i hi a)
      rw [WilsonIndependentMatchedVacant.joined X.vesselsC X.m (X.m+i) X.N l r
        (Nat.le_add_right ..) hni _ _ gone]
      exact WilsonIndependentMatchedVacant.zero (mul_nonneg
        (mul_nonneg Mpos (Real.rpow_nonneg hz.le _)) (Real.rpow_nonneg (div_nonneg top.le hz.le) _))
  have removed:=WilsonIndependentMatchedCoverFlush.original X.vesselsC l r X.m X.N X.i u b (d₁+d₂)
    (n₁+n₂) endDate P Q book (ca.head 0 (Nat.zero_le _)) (ca.head _ le_rfl) (cb.head 0 (Nat.zero_le _))
    (cb.head _ le_rfl) δ M top Mpos clear each
  have remained:=(fringedMat (Fringed.same ca.home (ca.head _ (Nat.zero_le _)) (le_refl 0))
    (Fringed.same cb.home (cb.head _ (Nat.zero_le _)) (le_refl 0)) zero_le_one le_rfl).f_l
  have all:=add remained removed.2
  rw [add_sub_cancel] at all
  have combine:δ^α*δ^β=δ^(((n₁+n₂:ℕ):ℝ)/4):=by rw [←Real.rpow_add top,expn]
  constructor
  · exact cruising X.ax X.vesselsC.hG X.vesselsC.green (Nat.le_add_right _ _) endDate
      ((ca.head _ le_rfl).manor (cb.head _ le_rfl))
  · convert all using 1
    unfold rate WilsonIndependentMatchedCoverHome.bill
    rw [←combine];dsimp only [M,α,β];ring

end YM.Integration.WilsonIndependentMatchedCoverReception
